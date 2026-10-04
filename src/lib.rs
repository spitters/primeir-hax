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
//! (`PolyOp`), with the accumulated product `basemul_acc`; plus the
//! constant-time family [`ct::CtField`], the square-root-of-a-ratio op
//! [`sqrt::SqrtRatio`] (RFC 9380, Appendix F.2.1), the extension-field family
//! [`ext::ExtField`] (`towerDialect`), the binary-field family
//! [`binary::BinaryField`] (`gf2Dialect`) and the rounding family
//! [`rounding::Rounding`] of ML-KEM and ML-DSA.
//!
//! `names.toml` at the crate root is the name manifest: for each trait item,
//! its qualified path, its arity and its op key. `tests/names_manifest.rs`
//! checks it against the trait declarations and against the def paths of
//! `hax_frontend_export.json`.
//! Reference instances: `fp25519` for `Field`, `ModArith`, `EcGroup`,
//! `CtField` and `SqrtRatio`; `fp256` (the NIST P-256 prime) for `Field`,
//! `ModArith`, `CtField` and `SqrtRatio`; `mldsa_q` (the ML-DSA modulus
//! `q = 8380417` and `Z_q[X]/(X^256 + 1)`) for `Field`, `ModArith` and
//! `PolyRing`; and `mlkem_q` (the ML-KEM modulus `q = 3329`
//! and the same ring, with the incomplete 7-layer transform of FIPS 203) for
//! `Field`, `PolyRing` and `Rounding` (as is `mldsa_q`); `ext_ref` (the tower
//! `Fp2`/`Fp6`/`Fp12` over `2^31 − 1`) for `ExtField`; and `gf128` (GF(2^128)
//! at the GHASH and the POLYVAL modulus) for `BinaryField`. [`poly_laws`]
//! holds the law suite of
//! the lattice surface as generic checks, which both lattice instances pass,
//! and [`laws`] states each algebraic law of the traits once, as a Boolean
//! function that those checks assert and the extraction carries.
//!
//! ## Features
//!
//! `bigint-instances` (default) carries `fp25519` and `fp256`, which are
//! realised with `num-bigint`. Without it the crate is the trait surface plus
//! the lattice instances `mldsa_q` and `mlkem_q`, `ext_ref`, `gf128` and the
//! law suite [`poly_laws`], is `no_std` and depends on `hax-lib` only; that is
//! how a `no_std` crate implements the traits for its own types.
//!
//! `fixed-width-instances` adds `fp256_mont` under rustc. `fieldmodel-witness`
//! puts `fp256_mont` on the extraction surface; it is the only way the module
//! reaches an extraction, so the export the compiler reads (default features)
//! carries no hand-written P-256 arithmetic.

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
/// | `from_bytes`/`write_bytes` | (de)serialization at the field boundary |
///
/// The modulus is an item of the instance, [`Field::MODULUS_LE`], so a
/// compiler reads `p` from the instance at each call site, and a function may
/// use two fields. The byte codec has the width [`Field::BYTES`] of the
/// instance: [`Field::write_bytes`] writes into a caller-supplied slice,
/// because stable Rust cannot use an associated constant as the length of a
/// returned array. [`to_byte_array`] is the array form for a width known at
/// the call site.
pub trait Field: Copy + Clone + PartialEq {
    /// The additive identity (`FieldOp` unit).
    const ZERO: Self;
    /// The multiplicative identity (`FieldOp` unit).
    const ONE: Self;
    /// The modulus `p`, as little-endian `u64` limbs whose last limb is
    /// nonzero. `crate::laws::modulus_law` ties it to the arithmetic: the
    /// encoding of `ZERO − ONE` is `p − 1`.
    const MODULUS_LE: &'static [u64];
    /// The length in bytes of the canonical encoding, `⌈bitlen(p) / 8⌉`
    /// (`crate::laws::bytes_width_law`).
    const BYTES: usize;

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
    /// Little-endian decode into the field (reduced mod p), of any length.
    fn from_bytes(bytes: &[u8]) -> Self;
    /// Little-endian encode of the canonical representative in `[0, p)` into
    /// `out[0..BYTES]`. Requires `out.len() >= BYTES`; `out[BYTES..]` is left
    /// unchanged. `from_bytes` inverts it (`crate::laws::bytes_roundtrip_law`).
    fn write_bytes(self, out: &mut [u8]);
}

/// The canonical encoding of `a` as an array of `B` bytes, zero beyond
/// [`Field::BYTES`]. Panics if `B < F::BYTES`. A convenience for callers that
/// know the width; gated out of the extraction, which sees
/// [`Field::write_bytes`].
#[cfg(not(hax))]
pub fn to_byte_array<F: Field, const B: usize>(a: F) -> [u8; B] {
    assert!(B >= F::BYTES, "to_byte_array: the array is shorter than Field::BYTES");
    let mut out = [0u8; B];
    a.write_bytes(&mut out);
    out
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

// --- Per-operation generic callers ------------------------------------------
//
// One generic function per `Field` operation, each a single trait-method call,
// plus two compositions. They are source programs for the field route of the
// compiler: each is a call site of an operation at a type parameter, so the
// extraction carries the operation by trait and method name and an instance
// supplies the arithmetic. Not `#[cfg]`-gated: the extraction must see them.

/// Field addition `a + b` ([`Field::add`]).
pub fn fe_add<F: Field>(a: F, b: F) -> F {
    a.add(b)
}

/// Field subtraction `a − b` ([`Field::sub`]).
pub fn fe_sub<F: Field>(a: F, b: F) -> F {
    a.sub(b)
}

/// Field negation `−a` ([`Field::neg`]).
pub fn fe_neg<F: Field>(a: F) -> F {
    a.neg()
}

/// Field multiplication `a·b` ([`Field::mul`]).
pub fn fe_mul<F: Field>(a: F, b: F) -> F {
    a.mul(b)
}

/// Squaring `a·a` ([`Field::square`]).
pub fn fe_sq<F: Field>(a: F) -> F {
    a.square()
}

/// Doubling `a + a` ([`Field::double`]).
pub fn fe_double<F: Field>(a: F) -> F {
    a.double()
}

/// Multiplicative inverse `a⁻¹` ([`Field::inv`]); `fe_inv(ZERO)` is
/// unspecified, as for the trait method.
pub fn fe_inv<F: Field>(a: F) -> F {
    a.inv()
}

/// The composition `a·b + c`: a multiplication whose result feeds an addition.
pub fn fe_mul_add<F: Field>(a: F, b: F, c: F) -> F {
    a.mul(b).add(c)
}

/// Division `a·b⁻¹` for `b ≠ 0`: an inversion whose result feeds a
/// multiplication.
pub fn fe_div<F: Field>(a: F, b: F) -> F {
    a.mul(b.inv())
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
/// limbs: the value of `Fp25519::MODULUS_LE`. The compiler reads the modulus
/// from the instance ([`Field::MODULUS_LE`]); this constant is the value the
/// reference instance uses.
pub const FIELD_MODULUS_25519: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFED,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0x7FFF_FFFF_FFFF_FFFF,
];

/// The field modulus of the NIST P-256 reference,
/// `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`
/// `  = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff`,
/// as four little-endian `u64` limbs: the value of `Fp256::MODULUS_LE`.
pub const FIELD_MODULUS_P256: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

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
// limbs, no allocation and no dependency. Written in hax's input subset. It is
// not part of the compiler's input: an extraction sees it only with the
// `fieldmodel-witness` feature, which produces the export behind the
// `FieldModel` witness. Under rustc `fixed-width-instances` enables it.
#[cfg(any(
    all(not(hax), feature = "fixed-width-instances"),
    all(hax, feature = "fieldmodel-witness")
))]
pub mod fp256_mont;

// The polynomial-ring op family (`PolyOp`), on the extraction surface.
pub mod poly;
pub mod ct;
// The square-root-of-a-ratio op (`SqrtRatio`, RFC 9380, Appendix F.2.1), on
// the extraction surface; its reference instances are gated inside the module.
pub mod sqrt;
// The extension-field op family (`towerDialect`), on the extraction surface.
pub mod ext;
// The binary-field op family (`gf2Dialect`), on the extraction surface.
pub mod binary;
// The rounding and compression op family of the lattice schemes, on the
// extraction surface; its instances are `mldsa_q` and `mlkem_q`.
pub mod rounding;

// The reference instance of `ExtField`: the tower Fp2/Fp6/Fp12 over the
// Mersenne prime 2^31 - 1, gated out of the extraction.
#[cfg(not(hax))]
pub mod ext_ref;

// The reference instances of `BinaryField`: GF(2^128) at the GHASH and at the
// POLYVAL modulus, gated out of the extraction.
#[cfg(not(hax))]
pub mod gf128;

// The reference instance of `PolyRing` (and `Field`, `ModArith`, `Rounding`)
// at the ML-DSA modulus: an opaque arithmetic leaf, gated out of the
// extraction like `fp25519`.
#[cfg(not(hax))]
pub mod mldsa_q;

// The reference instance at the ML-KEM modulus, whose transform is incomplete:
// an opaque arithmetic leaf, gated out of the extraction like `mldsa_q`.
#[cfg(not(hax))]
pub mod mlkem_q;

// The algebraic laws of the traits, one Boolean function per law, on the
// extraction surface: the test suites assert them under rustc and the
// extraction carries their definitions.
pub mod laws;

// The law suite of the lattice surface, run against an instance. Test support
// under rustc, gated out of the extraction.
#[cfg(not(hax))]
pub mod poly_laws;

// The per-operation callers against an integer reference: at the ML-DSA
// modulus over `u64` residues, and at `2^255 - 19` on operands small enough
// that the exact integer result is below the modulus.
#[cfg(all(test, not(hax)))]
mod caller_tests {
    use super::*;
    use crate::mldsa_q::Fq;

    const Q: u64 = poly::MODULUS_MLDSA as u64;

    /// Pseudorandom residues modulo `Q`, with `0`, `1` and `Q - 1`.
    fn samples() -> [u64; 35] {
        let mut out = [0u64; 35];
        out[1] = 1;
        out[2] = Q - 1;
        let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
        for x in out.iter_mut().skip(3) {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            *x = s % Q;
        }
        out
    }

    fn pow_mod(mut b: u64, mut e: u64) -> u64 {
        let mut acc = 1u64;
        b %= Q;
        while e > 0 {
            if e & 1 == 1 {
                acc = acc * b % Q;
            }
            b = b * b % Q;
            e >>= 1;
        }
        acc
    }

    #[test]
    fn callers_match_integer_reference_mldsa_q() {
        let xs = samples();
        for &a in &xs {
            let fa = Fq::new(a);
            assert_eq!(fe_neg(fa), Fq::new((Q - a) % Q));
            assert_eq!(fe_sq(fa), Fq::new(a * a));
            assert_eq!(fe_double(fa), Fq::new(2 * a));
            if a != 0 {
                let ia = fe_inv(fa);
                assert_eq!(ia, Fq::new(pow_mod(a, Q - 2)));
                assert_eq!(fe_mul(fa, ia), Fq::ONE);
            }
            for &b in &xs {
                let fb = Fq::new(b);
                assert_eq!(fe_add(fa, fb), Fq::new(a + b));
                assert_eq!(fe_sub(fa, fb), Fq::new(a + Q - b));
                assert_eq!(fe_mul(fa, fb), Fq::new(a * b));
                if b != 0 {
                    assert_eq!(fe_div(fa, fb), Fq::new(a * pow_mod(b, Q - 2)));
                }
                for &c in xs.iter().take(8) {
                    let fc = Fq::new(c);
                    assert_eq!(fe_mul_add(fa, fb, fc), Fq::new(a * b % Q + c));
                }
            }
        }
    }

    #[cfg(feature = "bigint-instances")]
    #[test]
    fn callers_match_integer_reference_fp25519() {
        use crate::fp25519::Fp25519;
        let e = Fp25519::from_u64;
        let (a, b, c) = (0xDEAD_BEEFu64, 0x1234_5678u64, 0xCAFEu64);
        assert_eq!(fe_add(e(a), e(b)), e(a + b));
        assert_eq!(fe_sub(e(a), e(b)), e(a - b));
        assert_eq!(fe_add(fe_neg(e(a)), e(a)), Fp25519::ZERO);
        assert_eq!(fe_mul(e(a), e(b)), e(a * b));
        assert_eq!(fe_sq(e(b)), e(b * b));
        assert_eq!(fe_double(e(a)), e(2 * a));
        assert_eq!(fe_mul(fe_inv(e(a)), e(a)), Fp25519::ONE);
        assert_eq!(fe_mul_add(e(a), e(b), e(c)), e(a * b + c));
        assert_eq!(fe_div(e(a * b), e(b)), e(a));
        // `field_demo` is `fe_mul_add` with `c = x`.
        assert_eq!(field_demo(e(a), e(b)), fe_mul_add(e(a), e(b), e(a)));
    }
}
