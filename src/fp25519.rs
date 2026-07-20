//! Reference instance — the **opaque arithmetic leaf**.
//!
//! `Fp25519` is the prime field of order `p = 2^255 - 19` (the Curve25519 base
//! field), and `Edwards25519` is the twisted-Edwards curve `-x² + y² = 1 + d·x²y²`
//! over it (edwards25519, RFC 8032). Both are realized with `num-bigint`: correct,
//! small, and — crucially — **not** meant to be hax-friendly. This is the leaf
//! the extraction ignores (`#[cfg(not(hax))]` in `lib.rs`); its only job is to
//! make `cargo build`/`cargo test` run genuine arithmetic. A deployed build would
//! swap in the verified compiler's emitted kernel, a `crypto-bigint` limb impl, or
//! a fiat-crypto leaf — tied to this trait surface *by value*.
//!
//! This is genuine modular arithmetic, never a toy (no `mul = xor`, no small
//! modulus): the reductions are real `mod (2^255 - 19)`, and the curve law uses
//! the complete twisted-Edwards addition formulas.

use crate::{EcGroup, Field, ModArith, Scalar};
use num_bigint::BigUint;

// --- prime and Montgomery constants ----------------------------------------

/// `p = 2^255 - 19`.
fn p() -> BigUint {
    (BigUint::from(1u8) << 255) - BigUint::from(19u8)
}

/// Montgomery radix `R = 2^256 mod p`.
fn mont_r() -> BigUint {
    (BigUint::from(1u8) << 256) % p()
}

/// `R⁻¹ mod p`.
fn mont_r_inv() -> BigUint {
    // R^{-1} = R^{p-2} mod p (Fermat), p prime.
    let p = p();
    mont_r().modpow(&(&p - BigUint::from(2u8)), &p)
}

// --- Fp25519 ----------------------------------------------------------------

/// An element of `GF(2^255 - 19)`, stored as its canonical little-endian
/// representative in `[0, p)`. `[u8; 32]` is `Copy`, so `Fp25519` satisfies the
/// `Field: Copy` bound while the arithmetic is done in `num-bigint`.
#[derive(Clone, Copy, Debug)]
pub struct Fp25519(pub [u8; 32]);

impl PartialEq for Fp25519 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for Fp25519 {}

impl Fp25519 {
    fn to_big(self) -> BigUint {
        BigUint::from_bytes_le(&self.0)
    }
    fn from_big(x: BigUint) -> Self {
        let r = x % p();
        let mut out = [0u8; 32];
        let le = r.to_bytes_le();
        out[..le.len()].copy_from_slice(&le);
        Fp25519(out)
    }
    /// Small-integer constructor (reduced mod p). Handy for tests.
    pub fn from_u64(n: u64) -> Self {
        Fp25519::from_big(BigUint::from(n))
    }
}

impl Field for Fp25519 {
    const ZERO: Self = Fp25519([0u8; 32]);
    const ONE: Self = Fp25519({
        let mut b = [0u8; 32];
        b[0] = 1;
        b
    });

    fn add(self, rhs: Self) -> Self {
        Fp25519::from_big(self.to_big() + rhs.to_big())
    }
    fn sub(self, rhs: Self) -> Self {
        // (a - b) mod p, computed as (a + (p - b)) to stay in the naturals.
        Fp25519::from_big(self.to_big() + (p() - rhs.to_big()))
    }
    fn mul(self, rhs: Self) -> Self {
        Fp25519::from_big(self.to_big() * rhs.to_big())
    }
    fn neg(self) -> Self {
        Fp25519::from_big(p() - self.to_big() % p())
    }
    fn square(self) -> Self {
        let a = self.to_big();
        Fp25519::from_big(&a * &a)
    }
    fn double(self) -> Self {
        let a = self.to_big();
        Fp25519::from_big(&a + &a)
    }
    fn inv(self) -> Self {
        // a^{p-2} mod p (Fermat).
        let p = p();
        Fp25519::from_big(self.to_big().modpow(&(&p - BigUint::from(2u8)), &p))
    }
    fn pow(self, exp: &[u64]) -> Self {
        // Assemble the little-endian u64 limbs into a BigUint exponent.
        let mut e = BigUint::from(0u8);
        for (i, limb) in exp.iter().enumerate() {
            e += BigUint::from(*limb) << (64 * i);
        }
        Fp25519::from_big(self.to_big().modpow(&e, &p()))
    }
    fn from_bytes(bytes: &[u8]) -> Self {
        Fp25519::from_big(BigUint::from_bytes_le(bytes))
    }
    fn to_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl ModArith for Fp25519 {
    fn to_mont(self) -> Self {
        Fp25519::from_big(self.to_big() * mont_r())
    }
    fn from_mont(self) -> Self {
        Fp25519::from_big(self.to_big() * mont_r_inv())
    }
    fn mont_mul(self, rhs: Self) -> Self {
        Fp25519::from_big(self.to_big() * rhs.to_big() * mont_r_inv())
    }
}

// --- Edwards25519 -----------------------------------------------------------

/// Curve parameter `d = -121665/121666 mod p` (RFC 8032, edwards25519).
fn ed_d() -> Fp25519 {
    Fp25519::from_big(
        BigUint::parse_bytes(
            b"37095705934669439343138083508754565189542113879843219016388785533085940283555",
            10,
        )
        .unwrap(),
    )
}

/// A point on edwards25519 in affine coordinates. `a = -1`, so the twisted
/// Edwards addition law is **complete** (no exceptional cases): the identity is
/// `(0, 1)` and every input pair adds correctly.
#[derive(Clone, Copy, Debug)]
pub struct Edwards25519 {
    pub x: Fp25519,
    pub y: Fp25519,
}

impl PartialEq for Edwards25519 {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}
impl Eq for Edwards25519 {}

impl Edwards25519 {
    /// The RFC 8032 base point `B` (prime-order generator).
    pub fn base_point() -> Self {
        let bx = Fp25519::from_big(
            BigUint::parse_bytes(
                b"15112221349535400772501151409588531511454012693041857206046113283949847762202",
                10,
            )
            .unwrap(),
        );
        let by = Fp25519::from_big(
            BigUint::parse_bytes(
                b"46316835694926478169428394003475163141307993866256225615783033603165251855960",
                10,
            )
            .unwrap(),
        );
        Edwards25519 { x: bx, y: by }
    }
}

impl EcGroup for Edwards25519 {
    type F = Fp25519;

    const IDENTITY: Self = Edwards25519 {
        x: Fp25519::ZERO,
        y: Fp25519::ONE,
    };

    fn point_add(self, rhs: Self) -> Self {
        // Complete twisted-Edwards addition, a = -1:
        //   x3 = (x1·y2 + y1·x2) / (1 + d·x1·x2·y1·y2)
        //   y3 = (y1·y2 + x1·x2) / (1 - d·x1·x2·y1·y2)
        let d = ed_d();
        let x1y2 = self.x.mul(rhs.y);
        let y1x2 = self.y.mul(rhs.x);
        let y1y2 = self.y.mul(rhs.y);
        let x1x2 = self.x.mul(rhs.x);
        let dxy = d.mul(x1x2).mul(y1y2);
        let x3 = x1y2.add(y1x2).mul(Fp25519::ONE.add(dxy).inv());
        let y3 = y1y2.add(x1x2).mul(Fp25519::ONE.sub(dxy).inv());
        Edwards25519 { x: x3, y: y3 }
    }

    fn point_double(self) -> Self {
        self.point_add(self)
    }

    fn scalar_mul(self, k: Scalar) -> Self {
        // Double-and-add over the (declassified, inside the opaque leaf) scalar
        // bits. In a CT emitted kernel the add would be a constant-time select;
        // here in the opaque leaf we compute the value plainly. `k.bit` keeps the
        // secret discipline visible at the API even though the leaf is opaque.
        let mut acc = Self::IDENTITY;
        // 253 bits suffice for scalars below the group order 2^252 + ...; iterate
        // the full 256 bits of the representation to be safe.
        for i in (0..256).rev() {
            acc = acc.point_double();
            if k.bit(i) {
                acc = acc.point_add(self);
            }
        }
        acc
    }

    fn to_affine(self) -> (Fp25519, Fp25519) {
        (self.x, self.y)
    }
}
