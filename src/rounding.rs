//! The rounding and compression op family of the lattice schemes.
//!
//! [`Rounding`] names the operations of FIPS 203 Section 4.2.1 (`Compress_d`,
//! `Decompress_d`) and FIPS 204 Section 7.4 (`Power2Round`, `Decompose`,
//! `HighBits`, `LowBits`, `MakeHint`, `UseHint`) on a coefficient field
//! `Z_q`, the source names of the ROUND-CODEC templates. As for the other
//! families, each method carries the name of the operation it denotes, and the
//! realisation stays an opaque arithmetic leaf.
//!
//! The integer results are those of the standards: a compressed value in
//! `[0, 2^d)`, a high part `r1 ≥ 0` as `u32`, a low part `r0` as a centred
//! `i32`. The instances are `crate::mldsa_q::Fq` and `crate::mlkem_q::Fq`; the
//! integer reference computation they share is [`reference`], gated out of the
//! extraction.

use crate::Field;

/// A prime field `Z_q` with a single-limb modulus `q < 2^31` and the rounding
/// operations of FIPS 203 and FIPS 204.
///
/// # The contract
///
/// Write `q` for `MODULUS_LE[0]`, `r⁺` for the representative of `r` in
/// `[0, q)`, `⌈·⌋` for rounding to the nearest integer with ties up, and
/// `x mod± m` for the representative of `x` in `(−m/2, m/2]`. For `d ≥ 1`
/// with `2^d < q` and `γ2` dividing `(q − 1)/2`:
///
/// 1. `compress_d(r, d) = ⌈(2^d / q)·r⁺⌋ mod 2^d` and `decompress_d(y, d) =
///    ⌈(q / 2^d)·y⌋` (FIPS 203, (4.7) and (4.8)); so
///    `compress_d(decompress_d(y, d), d) == y` for `y < 2^d`, and
///    `decompress_d(compress_d(r, d), d) − r mod± q` is at most
///    `⌈q / 2^(d+1)⌋` in absolute value.
/// 2. `power2round(r, d) = (r1, r0)` with `r0 = r⁺ mod± 2^d` and
///    `r1 = (r⁺ − r0) / 2^d` (FIPS 204, Algorithm 35).
/// 3. `decompose(r, γ2) = (r1, r0)` as in FIPS 204, Algorithm 36:
///    `r0 = r⁺ mod± 2γ2`, `r1 = (r⁺ − r0) / 2γ2`, except that `r⁺ − r0 =
///    q − 1` gives `(0, r0 − 1)`. `high_bits` and `low_bits` are its two
///    components (Algorithms 37 and 38).
/// 4. `make_hint(z, r, γ2)` is `high_bits(r) ≠ high_bits(r + z)` and
///    `use_hint` is Algorithm 40; for `|z mod± q| ≤ γ2`,
///    `use_hint(make_hint(z, r, γ2), r, γ2) == high_bits(r + z, γ2)`
///    (Lemma 1 of the CRYSTALS-Dilithium specification, with `α = 2γ2`).
///
/// `crate::laws` states these as Boolean functions.
pub trait Rounding: Field {
    /// `Compress_d` (FIPS 203, (4.7)).
    fn compress_d(self, d: u32) -> u32;
    /// `Decompress_d` (FIPS 203, (4.8)).
    fn decompress_d(y: u32, d: u32) -> Self;
    /// `Power2Round` (FIPS 204, Algorithm 35): `(r1, r0)`.
    fn power2round(self, d: u32) -> (u32, i32);
    /// `Decompose` (FIPS 204, Algorithm 36): `(r1, r0)`.
    fn decompose(self, gamma2: u32) -> (u32, i32);
    /// `HighBits` (FIPS 204, Algorithm 37).
    fn high_bits(self, gamma2: u32) -> u32;
    /// `LowBits` (FIPS 204, Algorithm 38).
    fn low_bits(self, gamma2: u32) -> i32;
    /// `MakeHint` (FIPS 204, Algorithm 39).
    fn make_hint(z: Self, r: Self, gamma2: u32) -> bool;
    /// `UseHint` (FIPS 204, Algorithm 40).
    fn use_hint(h: bool, r: Self, gamma2: u32) -> u32;
}

/// A generic caller of [`Rounding::compress_d`] and
/// [`Rounding::decompress_d`]: the round trip through `d` bits, as ML-KEM
/// encryption and decryption compute it. Not `cfg`-gated: the extraction must
/// see it.
pub fn compress_roundtrip_demo<F: Rounding>(a: F, d: u32) -> F {
    F::decompress_d(a.compress_d(d), d)
}

/// A generic caller of [`Rounding::make_hint`] and [`Rounding::use_hint`]:
/// the high part of `r + z` recovered from `r` and the hint, as ML-DSA
/// verification computes it.
pub fn hint_demo<F: Rounding>(z: F, r: F, gamma2: u32) -> u32 {
    F::use_hint(F::make_hint(z, r, gamma2), r, gamma2)
}

/// A generic caller of [`Rounding::power2round`]: the high part of `t`, as
/// ML-DSA key generation computes `t1`.
pub fn power2round_demo<F: Rounding>(t: F, d: u32) -> u32 {
    t.power2round(d).0
}

/// The integer computation of the operations, on a canonical representative
/// `r ∈ [0, q)`, shared by the instances. Gated out of the extraction.
#[cfg(not(hax))]
pub mod reference {
    /// `⌈(2^d / q)·r⌋ mod 2^d`.
    pub fn compress(q: u64, r: u64, d: u32) -> u32 {
        ((((r << (d + 1)) + q) / (2 * q)) & ((1u64 << d) - 1)) as u32
    }

    /// `⌈(q / 2^d)·y⌋`, a representative in `[0, q]`; the caller reduces it.
    pub fn decompress(q: u64, y: u32, d: u32) -> u64 {
        (2 * (y as u64) * q + (1u64 << d)) >> (d + 1)
    }

    /// `x mod± m` for an even `m`: the representative in `(−m/2, m/2]`.
    fn mod_pm(x: u64, m: u64) -> i64 {
        let t = (x % m) as i64;
        if t > (m / 2) as i64 {
            t - m as i64
        } else {
            t
        }
    }

    /// FIPS 204, Algorithm 35.
    pub fn power2round(r: u64, d: u32) -> (u32, i32) {
        let r0 = mod_pm(r, 1u64 << d);
        (((r as i64 - r0) >> d) as u32, r0 as i32)
    }

    /// FIPS 204, Algorithm 36.
    pub fn decompose(q: u64, r: u64, gamma2: u32) -> (u32, i32) {
        let m = 2 * gamma2 as u64;
        let r0 = mod_pm(r, m);
        if r as i64 - r0 == q as i64 - 1 {
            (0, (r0 - 1) as i32)
        } else {
            (((r as i64 - r0) / m as i64) as u32, r0 as i32)
        }
    }

    /// FIPS 204, Algorithm 40.
    pub fn use_hint(q: u64, h: bool, r: u64, gamma2: u32) -> u32 {
        let m = ((q - 1) / (2 * gamma2 as u64)) as u32;
        let (r1, r0) = decompose(q, r, gamma2);
        if h && r0 > 0 {
            (r1 + 1) % m
        } else if h {
            (r1 + m - 1) % m
        } else {
            r1
        }
    }
}
