//! # `primeir-hax` — the prime-IR trait surface at the hax level
//!
//! A **stable-Rust**, nominally-recognizable surface for prime-field /
//! modular-arithmetic / elliptic-curve arithmetic. The traits here are the
//! source-level analogue of the VIR prime-IR correspondence dialect ops
//! (`FieldOp` / `FieldDerivedOps` / `ModArithMont` / `montInverse` / `ECOp` /
//! `EcConvertOps`): each trait method is named after the dialect op-family it is
//! meant to map to, so `haxpipeT` can recognize a call **nominally** (by trait +
//! method name, at the same `Adt`/impl site the secret-integer axis uses) and
//! emit the corresponding prime-IR dialect op — *without reconstructing the op
//! identity from limb-and-loop code*.
//!
//! ## Dual-use (the whole point, exactly as for `secret_integers`)
//!
//! * **rustc**: these are ordinary Rust traits with a real concrete instance
//!   (`fp25519::Fp25519` over the Curve25519 prime `2^255 - 19`). `cargo build`
//!   and `cargo test` run genuine arithmetic. There are **no** compiler
//!   intrinsics (`core::intrinsics` / `#[rustc_intrinsic]`) and **no** nightly
//!   features — plain stable Rust, so the Role-3 KATs run under rustc.
//! * **hax**: `cargo hax into lean` extracts the *trait surface* (the op
//!   identities). The concrete impl body is the **opaque arithmetic leaf** — the
//!   extraction ignores it; its bytes come from the owned/verified kernel
//!   underneath, tied *by value*, never front-compiled from limb code.
//!
//! ## Where the instances come from
//!
//! A `Field`/`ModArith`/`EcGroup` impl can be realized several ways — the
//! verified compiler emitting Rust, a bignum library (`crypto-bigint`,
//! `num-bigint`), or fiat-crypto. This crate ships **one reference instance**
//! (`num-bigint`-backed `Fp25519`, plus an `Edwards25519` demo group) so the
//! surface compiles and the KATs pass. The identity of the leaf is *declared* by
//! the trait; the realization is interchangeable.
//!
//! ## The constant-time axis (secret scalar)
//!
//! The scalar of `EcGroup::scalar_mul` is **secret**, so it is taken as
//! [`Scalar`] — a documented secret newtype whose only escape is
//! [`Scalar::declassify`] (the audited trusted downgrade, mirroring `ctdemo-hax`
//! `U8`). This is where the prime-IR axis meets the CT axis: a data-dependent use
//! of the scalar must be rejected by `cmdCT`, and the secrecy marker is carried
//! in the *type*, recognized nominally at the same site as `secret_integers`.
//!
//! ## Scope
//!
//! Four trait families: Field / ModArith / EC here, and the polynomial-ring
//! family [`poly::PolyRing`] (`ntt`, `intt`, `basemul`, `ntt_add`, `ntt_sub`,
//! `poly_add`, `poly_sub`, `poly_smul`, `ntt_mul`, and the construction of an
//! element in NTT form entry by entry, as a sampler in NTT form does), which
//! names the operations of the `polyDialect`
//! (`PolyOp`); plus the constant-time family [`ct::CtField`] and the
//! square-root-of-a-ratio op [`sqrt::SqrtRatio`] (RFC 9380, Appendix F.2.1).
//! Reference instances: `fp25519` for `Field`, `ModArith`, `EcGroup`,
//! `CtField` and `SqrtRatio`; `fp256` (the NIST P-256 prime) for `Field`,
//! `ModArith`, `CtField` and `SqrtRatio`; `mldsa_q` (the ML-DSA modulus
//! `q = 8380417` and `Z_q[X]/(X^256 + 1)`) for `Field`, `ModArith` and
//! `PolyRing`; and `mlkem_q` (the ML-KEM modulus `q = 3329`
//! and the same ring, with the incomplete 7-layer transform of FIPS 203) for
//! `Field` and `PolyRing`. [`poly_laws`] holds the law suite of
//! the lattice surface as generic checks, which both lattice instances pass.
//!
//! ## Features
//!
//! `bigint-instances` (default) carries `fp25519` and `fp256`, which are
//! realised with `num-bigint`. Without it the crate is the trait surface plus
//! the two lattice instances `mldsa_q` and `mlkem_q` and the law suite
//! [`poly_laws`], is `no_std` and has no dependency; that is how a `no_std`
//! crate implements the traits for its own types.

#![forbid(unsafe_code)]
// Without the `bigint-instances` feature the crate is the trait surface plus
// the `mldsa_q` instance, which use `core` only.
#![cfg_attr(not(feature = "bigint-instances"), no_std)]
// Stable Rust only: no intrinsics, no nightly features. `autoImplicit`-style
// strictness is a Lean concern; here we just keep the surface plain.

/// A prime field element. Mirrors hacspec-lib's `FieldElement` shape, but
/// crypto-sized (the concrete instance is a 255-bit field, not `u16`).
///
/// Method names align with the prime-IR dialect op-families so the extraction
/// can map them nominally:
///
/// | method              | prime-IR op-family                         |
/// |---------------------|--------------------------------------------|
/// | `add`/`sub`/`mul`/`neg` | `FieldOp` (`fAddF`/`fSubF`/`fMulF`/`fNegF`) |
/// | `square`/`double`   | `FieldDerivedOps` (`fieldSquareF`/`fieldDoubleF`) |
/// | `inv`               | `montInverse`                              |
/// | `pow`               | `FieldDerivedOps.fieldPowF` (`powui`)      |
/// | `from_bytes`/`to_bytes` | (de)serialization at the field boundary |
///
/// `to_bytes` is fixed at 32 bytes: enough for any field up to 256 bits (the
/// `2^255-19` reference). A trait-generic width (`const BYTES`) is deferred —
/// stable Rust cannot use an associated const in a return-position array length.
pub trait Field: Copy + Clone + PartialEq {
    /// The additive identity (`FieldOp` unit).
    const ZERO: Self;
    /// The multiplicative identity (`FieldOp` unit).
    const ONE: Self;

    // --- FieldOp family -----------------------------------------------------
    /// Field addition. Maps to `FieldOp.fAdd`.
    fn add(self, rhs: Self) -> Self;
    /// Field subtraction. Maps to `FieldOp.fSub`.
    fn sub(self, rhs: Self) -> Self;
    /// Field multiplication. **The canonical nominal target** —
    /// `primeir::Field::mul` → `FieldOp.fMul`.
    fn mul(self, rhs: Self) -> Self;
    /// Field negation. Maps to `FieldOp.fNeg`.
    fn neg(self) -> Self;

    // --- FieldDerivedOps family --------------------------------------------
    /// Squaring `a ↦ a·a`. Maps to `FieldDerivedOps.fieldSquare`.
    fn square(self) -> Self;
    /// Doubling `a ↦ a + a`. Maps to `FieldDerivedOps.fieldDouble`.
    fn double(self) -> Self;

    // --- montInverse --------------------------------------------------------
    /// Multiplicative inverse (`inv(ZERO)` is unspecified). Maps to
    /// `montInverse`.
    fn inv(self) -> Self;

    // --- powui --------------------------------------------------------------
    /// Fixed-exponent power `a ↦ a ^ e`, `e` given little-endian as u64 limbs.
    /// Maps to `FieldDerivedOps.fieldPowF` (`powui`).
    fn pow(self, exp: &[u64]) -> Self;

    // --- serialization ------------------------------------------------------
    /// Little-endian decode into the field (reduced mod p).
    fn from_bytes(bytes: &[u8]) -> Self;
    /// Little-endian encode of the canonical representative (32 bytes).
    fn to_bytes(self) -> [u8; 32];
}

/// Montgomery-domain modular arithmetic on top of a [`Field`]. Maps to the
/// `ModArithMont` correspondence dialect.
///
/// The contract: `mont_mul(to_mont(a), to_mont(b)) == to_mont(a.mul(b))` and
/// `from_mont(to_mont(a)) == a`.
pub trait ModArith: Field {
    /// Map to the Montgomery domain `a ↦ a·R mod p`. `ModArithMont.toMont`.
    fn to_mont(self) -> Self;
    /// Map back from the Montgomery domain `a ↦ a·R⁻¹ mod p`.
    /// `ModArithMont.fromMont`.
    // The name is the dialect operation `fromMont`, which takes its argument.
    #[allow(clippy::wrong_self_convention)]
    fn from_mont(self) -> Self;
    /// Montgomery multiplication `(a, b) ↦ a·b·R⁻¹ mod p`.
    /// `ModArithMont.montMul`.
    fn mont_mul(self, rhs: Self) -> Self;
}

/// An elliptic-curve group. Maps to the `ECOp` op-family (`point_add`,
/// `point_double`, `scalar_mul`) plus `EcConvertOps` (`to_affine`).
///
/// The scalar of [`EcGroup::scalar_mul`] is **secret** — see [`Scalar`].
pub trait EcGroup: Copy + Clone + PartialEq {
    /// The coordinate field.
    type F: Field;

    /// The group identity (point at infinity / neutral element).
    const IDENTITY: Self;

    /// Group addition. Maps to `ECOp.pointAdd` (e.g. `p256_point_add`,
    /// `g1_add`).
    fn point_add(self, rhs: Self) -> Self;
    /// Point doubling `P ↦ 2P`. Maps to `ECOp.pointDouble`.
    fn point_double(self) -> Self;
    /// Scalar multiplication `[k]P` with a **secret** scalar `k`. Maps to
    /// `ECOp.scalarMul` (e.g. `g1_scalar_mul`). The ladder must be a
    /// data-independent CT double-and-add; a data-dependent variant is rejected
    /// by `cmdCT` because `k : Scalar` is secret.
    fn scalar_mul(self, k: Scalar) -> Self;
    /// Convert to affine `(x, y)` coordinates. Maps to
    /// `EcConvertOps` (Jacobian→affine).
    fn to_affine(self) -> (Self::F, Self::F);
}

/// A **secret** scalar (e.g. an ECDH/EdDSA private scalar). The secrecy marker
/// is carried in the *type*: the only way out is [`Scalar::declassify`], the
/// single audited Secret→Public downgrade (mirroring `ctdemo-hax`'s `U8` and the
/// `secret_integers` discipline). The extraction recognizes this newtype
/// nominally and emits it into the `_secrecy` table, so `cmdCT` fail-closes on
/// any data-dependent use.
///
/// SECRET: `cmdCT` must reject a branch / loop-guard / memory index / non-CT leaf
/// call whose operand traces to a `Scalar` that has not been `declassify`d.
#[derive(Clone, Copy)]
pub struct Scalar(pub(crate) [u8; 32]);

impl Scalar {
    /// Wrap 32 little-endian bytes as a secret scalar. This is an *ingress*
    /// (Public→Secret), always sound.
    pub fn from_bytes_secret(bytes: [u8; 32]) -> Self {
        Scalar(bytes)
    }

    /// The single Secret→Public transition — the audited trusted downgrade.
    /// Every use of the scalar bits outside a CT primitive must pass through
    /// here, so each is an explicit audit point (`scripts/declassify-audit.sh`).
    pub fn declassify(self) -> [u8; 32] {
        self.0
    }

    /// Little-endian bit `i` of the scalar. Still secret: returns a `bool` that
    /// the CT ladder consumes via a constant-time select, never a branch.
    /// (Provided as a convenience for CT double-and-add implementations.)
    pub fn bit(&self, i: usize) -> bool {
        let byte = self.0[i >> 3];
        ((byte >> (i & 7)) & 1) == 1
    }
}

/// A tiny generic caller that exercises the [`Field`] trait methods
/// **nominally**, so `cargo hax into lean` emits a call site for `Field::mul`
/// and `Field::add`. It is deliberately *not* `#[cfg]`-gated: the extraction
/// must see it. Computes `x·y + x`, so both the canonical `mul` target and an
/// `add` appear at recognizable trait-method call sites. The body is a pure
/// composition of trait ops — the identity of each op is declared by the
/// method name, the realization stays the opaque arithmetic leaf.
pub fn field_demo<F: Field>(x: F, y: F) -> F {
    x.mul(y).add(x)
}

/// A generic caller exercising [`ModArith::mont_mul`] **nominally**, so
/// `haxpipeT` emits a call site for the Montgomery multiply. Not `#[cfg]`-gated:
/// the extraction must see it. The body is a single trait-op call, so the op
/// identity is declared by the method name and the realization stays the opaque
/// arithmetic leaf.
pub fn modarith_demo<F: ModArith>(a: F, b: F) -> F {
    a.mont_mul(b)
}

/// A generic caller exercising [`EcGroup::point_add`] **nominally**, so
/// `haxpipeT` emits a call site for the group add. Not `#[cfg]`-gated: the
/// extraction must see it. The body is a single trait-op call, so the op
/// identity is declared by the method name and the realization stays the opaque
/// arithmetic leaf.
pub fn ec_demo<G: EcGroup>(p: G, q: G) -> G {
    p.point_add(q)
}

/// A generic caller exercising [`EcGroup::point_double`] **nominally**.
pub fn ec_double_demo<G: EcGroup>(p: G) -> G {
    p.point_double()
}

/// A generic caller exercising [`EcGroup::scalar_mul`] **nominally**, carrying a
/// **secret** [`Scalar`] `k` from the source signature through to the call site.
/// Not `#[cfg]`-gated: the extraction must see it. This is the CT axis end-to-end
/// witness — the `Scalar` parameter `k` is recognized nominally and lands in the
/// emitted `_secrecy` side table, so `cmdCT` fail-closes on any data-dependent use
/// of the scalar. The body is a single trait-op call; the ladder identity is
/// declared by the method name and the realization stays the opaque arithmetic
/// leaf.
pub fn scalar_mul_demo<G: EcGroup>(p: G, k: Scalar) -> G {
    p.scalar_mul(k)
}

/// The field modulus of the `2^255-19` reference, as four little-endian `u64`
/// limbs. A **hax-visible source constant**: `haxpipeT` emits the `pub const`
/// (top-level consts are on the extraction surface), so the modulus is carried
/// *from the source* rather than supplied only on the Lean side. The Lean
/// recognizer reconstructs `∑ limbᵢ·2^(64·i)` and ties it to the `p` the field
/// recognizers use, folding the modulus into the verified chain.
pub const FIELD_MODULUS_25519: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFED,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0x7FFF_FFFF_FFFF_FFFF,
];

/// Expose the modulus limbs, keeping [`FIELD_MODULUS_25519`] on the hax surface
/// (an unreferenced `const` can be dropped before extraction).
pub fn field_modulus_limbs() -> [u64; 4] {
    FIELD_MODULUS_25519
}

/// The field modulus of the NIST P-256 reference,
/// `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`
/// `  = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff`,
/// as four little-endian `u64` limbs. A hax-visible source constant in the
/// sense of [`FIELD_MODULUS_25519`].
pub const FIELD_MODULUS_P256: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

/// Expose the P-256 modulus limbs, keeping [`FIELD_MODULUS_P256`] on the hax
/// surface.
pub fn field_modulus_p256_limbs() -> [u64; 4] {
    FIELD_MODULUS_P256
}

// The concrete reference instance — the OPAQUE ARITHMETIC LEAF. It is gated out
// of the hax extraction (`cfg(not(hax))`): hax recognizes the trait surface
// above nominally and treats the realization as opaque, so the leaf body need
// not live in hax's input subset. Under plain rustc the module is present, so
// `cargo build` / `cargo test` exercise real 255-bit arithmetic.
#[cfg(all(not(hax), feature = "bigint-instances"))]
pub mod fp25519;

// The reference instance of the P-256 base field: an opaque arithmetic leaf,
// gated out of the extraction like `fp25519`.
#[cfg(all(not(hax), feature = "bigint-instances"))]
pub mod fp256;

// The fixed-width instance of the same field: four `u64` Montgomery-domain
// limbs, no allocation and no dependency. An opaque arithmetic leaf, gated out
// of the extraction like `fp256`.
#[cfg(all(not(hax), feature = "fixed-width-instances"))]
pub mod fp256_mont;

// The polynomial-ring op family (`PolyOp`), on the extraction surface.
pub mod poly;
pub mod ct;
// The square-root-of-a-ratio op (`SqrtRatio`, RFC 9380, Appendix F.2.1), on
// the extraction surface; its reference instances are gated inside the module.
pub mod sqrt;

// Its reference instance at the ML-DSA modulus: an opaque arithmetic leaf,
// gated out of the extraction like `fp25519`.
#[cfg(not(hax))]
pub mod mldsa_q;

// Its reference instance at the ML-KEM modulus, whose transform is incomplete:
// an opaque arithmetic leaf, gated out of the extraction like `mldsa_q`.
#[cfg(not(hax))]
pub mod mlkem_q;

// The law suite of the lattice surface, run against an instance. Test support
// under rustc, gated out of the extraction.
#[cfg(not(hax))]
pub mod poly_laws;
