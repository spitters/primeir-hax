//! Reference instance of the prime field of NIST P-256 — an **opaque
//! arithmetic leaf**.
//!
//! `Fp256` is the prime field of order `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`,
//! the base field of the curve P-256 (FIPS 186-4; RFC 9380, Section 8.2). It is
//! realized with `num-bigint`, like [`crate::fp25519::Fp25519`]: correct and
//! small, and not meant to be hax-friendly. The module is gated out of the
//! extraction (`#[cfg(not(hax))]` in `lib.rs`); its job is to make
//! `cargo build` / `cargo test` run the arithmetic of the field. A deployed
//! build swaps in an emitted kernel or a limb implementation, tied to the
//! trait surface by value.
//!
//! The reductions are `mod p` for the P-256 prime; the constant-time
//! operations of [`CtField`] are realized on the canonical representative with
//! `==` and `if`, so this instance is not constant-time (see `ct.rs`).

use crate::ct::CtField;
use crate::{Field, ModArith};
use num_bigint::BigUint;

// --- prime and Montgomery constants ----------------------------------------

/// `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`.
fn p() -> BigUint {
    (BigUint::from(1u8) << 256) - (BigUint::from(1u8) << 224) + (BigUint::from(1u8) << 192)
        + (BigUint::from(1u8) << 96)
        - BigUint::from(1u8)
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

// --- Fp256 ------------------------------------------------------------------

/// An element of `GF(p)` for the P-256 prime, stored as its canonical
/// little-endian representative in `[0, p)`. `[u8; 32]` is `Copy`, so `Fp256`
/// satisfies the `Field: Copy` bound while the arithmetic is done in
/// `num-bigint`.
#[derive(Clone, Copy, Debug)]
pub struct Fp256(pub [u8; 32]);

impl PartialEq for Fp256 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for Fp256 {}

impl Fp256 {
    fn to_big(self) -> BigUint {
        BigUint::from_bytes_le(&self.0)
    }
    fn from_big(x: BigUint) -> Self {
        let r = x % p();
        let mut out = [0u8; 32];
        let le = r.to_bytes_le();
        out[..le.len()].copy_from_slice(&le);
        Fp256(out)
    }
    /// Small-integer constructor (reduced mod p).
    pub fn from_u64(n: u64) -> Self {
        Fp256::from_big(BigUint::from(n))
    }
}

impl Field for Fp256 {
    const ZERO: Self = Fp256([0u8; 32]);
    const ONE: Self = Fp256({
        let mut b = [0u8; 32];
        b[0] = 1;
        b
    });

    fn add(self, rhs: Self) -> Self {
        Fp256::from_big(self.to_big() + rhs.to_big())
    }
    fn sub(self, rhs: Self) -> Self {
        // (a - b) mod p, computed as (a + (p - b)) to stay in the naturals.
        Fp256::from_big(self.to_big() + (p() - rhs.to_big()))
    }
    fn mul(self, rhs: Self) -> Self {
        Fp256::from_big(self.to_big() * rhs.to_big())
    }
    fn neg(self) -> Self {
        Fp256::from_big(p() - self.to_big() % p())
    }
    fn square(self) -> Self {
        let a = self.to_big();
        Fp256::from_big(&a * &a)
    }
    fn double(self) -> Self {
        let a = self.to_big();
        Fp256::from_big(&a + &a)
    }
    fn inv(self) -> Self {
        // a^{p-2} mod p (Fermat).
        let p = p();
        Fp256::from_big(self.to_big().modpow(&(&p - BigUint::from(2u8)), &p))
    }
    fn pow(self, exp: &[u64]) -> Self {
        // Assemble the little-endian u64 limbs into a BigUint exponent.
        let mut e = BigUint::from(0u8);
        for (i, limb) in exp.iter().enumerate() {
            e += BigUint::from(*limb) << (64 * i);
        }
        Fp256::from_big(self.to_big().modpow(&e, &p()))
    }
    fn from_bytes(bytes: &[u8]) -> Self {
        Fp256::from_big(BigUint::from_bytes_le(bytes))
    }
    fn to_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl ModArith for Fp256 {
    fn to_mont(self) -> Self {
        Fp256::from_big(self.to_big() * mont_r())
    }
    fn from_mont(self) -> Self {
        Fp256::from_big(self.to_big() * mont_r_inv())
    }
    fn mont_mul(self, rhs: Self) -> Self {
        Fp256::from_big(self.to_big() * rhs.to_big() * mont_r_inv())
    }
}

// The constant-time op family on the canonical 32-byte representative:
// comparison with `==`, selection with `if`; not constant-time (see `ct.rs`).
impl CtField for Fp256 {
    fn ct_select(cond: u64, then_v: Self, else_v: Self) -> Self {
        if cond == 1 {
            then_v
        } else {
            else_v
        }
    }

    fn ct_eq(self, rhs: Self) -> u64 {
        if self.0 == rhs.0 {
            1
        } else {
            0
        }
    }

    fn is_zero(self) -> u64 {
        self.ct_eq(Self::ZERO)
    }

    fn is_negative(self) -> u64 {
        (self.0[0] & 1) as u64
    }

    fn ct_abs(self) -> Self {
        Self::ct_select(self.is_negative(), self.neg(), self)
    }
}
