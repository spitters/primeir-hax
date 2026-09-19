//! Reference instance of the prime-IR surface at the ML-DSA modulus
//! `q = 8380417`: the field [`Fq`] ([`Field`], [`ModArith`] with `R = 2^32`) and
//! the ring [`PolyDsa`] = `Z_q[X]/(X^256 + 1)` ([`PolyRing`]) with the NTT of
//! FIPS 204 §7.5.
//!
//! This module is the opaque arithmetic leaf: it is gated out of the hax
//! extraction and exists so that the surface runs under rustc and its tests
//! compare it with the FIPS 204 specification crate.

// Indexed loops mirror the index-by-index statement of the algorithms.
#![allow(clippy::needless_range_loop)]

use crate::poly::{PolyRing, MODULUS_MLDSA};
use crate::{Field, ModArith};

const Q: u64 = MODULUS_MLDSA as u64;

/// ζ = 1753, a primitive 512th root of unity modulo q (FIPS 204 §7.5).
pub const ZETA: u32 = 1753;

/// `256⁻¹ mod q` (FIPS 204 Algorithm 42).
pub const INV_256: u32 = 8347681;

/// An element of `Z_q`, stored as its representative in `[0, q)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fq(pub u32);

impl Fq {
    /// The residue of `n` modulo q.
    pub fn new(n: u64) -> Self {
        Fq((n % Q) as u32)
    }

    fn pow_u64(self, mut e: u64) -> Self {
        let mut base = self;
        let mut acc = Fq(1);
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            e >>= 1;
        }
        acc
    }
}

impl Field for Fq {
    const ZERO: Self = Fq(0);
    const ONE: Self = Fq(1);

    fn add(self, rhs: Self) -> Self {
        Fq::new(self.0 as u64 + rhs.0 as u64)
    }
    fn sub(self, rhs: Self) -> Self {
        Fq::new(self.0 as u64 + Q - rhs.0 as u64)
    }
    fn mul(self, rhs: Self) -> Self {
        Fq::new(self.0 as u64 * rhs.0 as u64)
    }
    fn neg(self) -> Self {
        Fq::new(Q - self.0 as u64)
    }
    fn square(self) -> Self {
        self.mul(self)
    }
    fn double(self) -> Self {
        self.add(self)
    }
    fn inv(self) -> Self {
        // Fermat: a^(q−2).
        self.pow_u64(Q - 2)
    }
    fn pow(self, exp: &[u64]) -> Self {
        let mut acc = Fq(1);
        for limb in exp.iter().rev() {
            for bit in (0..64).rev() {
                acc = acc.mul(acc);
                if (limb >> bit) & 1 == 1 {
                    acc = acc.mul(self);
                }
            }
        }
        acc
    }
    fn from_bytes(bytes: &[u8]) -> Self {
        let mut acc = 0u64;
        for &b in bytes.iter().rev() {
            acc = (acc * 256 + b as u64) % Q;
        }
        Fq(acc as u32)
    }
    fn to_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..4].copy_from_slice(&self.0.to_le_bytes());
        out
    }
}

/// `R = 2^32 mod q`, the Montgomery radix of the 32-bit reference
/// implementations of ML-DSA.
pub const MONT_R: u32 = ((1u64 << 32) % Q) as u32;

impl ModArith for Fq {
    fn to_mont(self) -> Self {
        self.mul(Fq(MONT_R))
    }
    fn from_mont(self) -> Self {
        self.mul(Fq(MONT_R).inv())
    }
    fn mont_mul(self, rhs: Self) -> Self {
        self.mul(rhs).mul(Fq(MONT_R).inv())
    }
}

/// BitRev8 (FIPS 204 Algorithm 43).
pub fn bit_rev_8(n: usize) -> usize {
    let mut r = 0;
    let mut x = n;
    for _ in 0..8 {
        r = (r << 1) | (x & 1);
        x >>= 1;
    }
    r
}

/// `zetas[k] = ζ^BitRev8(k) mod q` (FIPS 204 Appendix B), for `1 <= k < 256`.
pub fn zeta_pow(k: usize) -> Fq {
    Fq(ZETA).pow_u64(bit_rev_8(k) as u64)
}

/// An element of `Z_q[X]/(X^256 + 1)` in coefficient form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolyDsa(pub [u32; 256]);

/// An element of `T_q` (FIPS 204 §2.3): an element of the ring in NTT form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NttDsa(pub [u32; 256]);

impl PolyRing for PolyDsa {
    type Coeff = Fq;
    type NttForm = NttDsa;
    const N: usize = 256;
    const ZERO: Self = PolyDsa([0u32; 256]);

    fn coeff(self, i: usize) -> Fq {
        Fq(self.0[i])
    }
    fn with_coeff(self, i: usize, c: Fq) -> Self {
        let mut w = self;
        w.0[i] = c.0;
        w
    }
    fn ntt_coeff(w: NttDsa, i: usize) -> Fq {
        Fq(w.0[i])
    }

    /// FIPS 204 Algorithm 41: `ŵ[i] = w(ζ^(2·BitRev8(i) + 1))`.
    fn ntt(self) -> NttDsa {
        let mut w = self.0;
        let mut m = 0usize;
        let mut len = 128usize;
        while len >= 1 {
            let mut start = 0usize;
            while start < 256 {
                m += 1;
                let z = zeta_pow(m);
                for j in start..start + len {
                    let t = z.mul(Fq(w[j + len]));
                    w[j + len] = Fq(w[j]).sub(t).0;
                    w[j] = Fq(w[j]).add(t).0;
                }
                start += 2 * len;
            }
            len /= 2;
        }
        NttDsa(w)
    }

    /// FIPS 204 Algorithm 42.
    fn intt(w_hat: NttDsa) -> Self {
        let mut w = w_hat.0;
        let mut m = 256usize;
        let mut len = 1usize;
        while len < 256 {
            let mut start = 0usize;
            while start < 256 {
                m -= 1;
                let z = zeta_pow(m).neg();
                for j in start..start + len {
                    let t = Fq(w[j]);
                    w[j] = t.add(Fq(w[j + len])).0;
                    w[j + len] = z.mul(t.sub(Fq(w[j + len]))).0;
                }
                start += 2 * len;
            }
            len *= 2;
        }
        for c in w.iter_mut() {
            *c = Fq(*c).mul(Fq(INV_256)).0;
        }
        PolyDsa(w)
    }

    /// FIPS 204 Algorithm 45 (MultiplyNTT): the coefficient-wise product.
    fn basemul(a: NttDsa, b: NttDsa) -> NttDsa {
        let mut w = [0u32; 256];
        for i in 0..256 {
            w[i] = Fq(a.0[i]).mul(Fq(b.0[i])).0;
        }
        NttDsa(w)
    }
    /// FIPS 204 Algorithm 44 (AddNTT).
    fn ntt_add(a: NttDsa, b: NttDsa) -> NttDsa {
        let mut w = [0u32; 256];
        for i in 0..256 {
            w[i] = Fq(a.0[i]).add(Fq(b.0[i])).0;
        }
        NttDsa(w)
    }
    fn poly_add(self, rhs: Self) -> Self {
        let mut w = [0u32; 256];
        for i in 0..256 {
            w[i] = Fq(self.0[i]).add(Fq(rhs.0[i])).0;
        }
        PolyDsa(w)
    }
    fn poly_sub(self, rhs: Self) -> Self {
        let mut w = [0u32; 256];
        for i in 0..256 {
            w[i] = Fq(self.0[i]).sub(Fq(rhs.0[i])).0;
        }
        PolyDsa(w)
    }
    fn poly_smul(self, c: Fq) -> Self {
        let mut w = [0u32; 256];
        for i in 0..256 {
            w[i] = c.mul(Fq(self.0[i])).0;
        }
        PolyDsa(w)
    }
    fn ntt_mul(self, rhs: Self) -> Self {
        Self::intt(Self::basemul(self.ntt(), rhs.ntt()))
    }
}
