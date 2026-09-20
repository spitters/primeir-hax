//! Reference instance of the prime-IR lattice surface at the ML-KEM modulus
//! `q = 3329`: the field [`Fq`] ([`Field`]) and the ring [`PolyKem`] =
//! `Z_q[X]/(X^256 + 1)` ([`PolyRing`]) with the NTT of FIPS 203 §4.3.
//!
//! The transform is **incomplete**: it runs 7 layers, not 8, so it splits
//! `X^256 + 1` into 128 quadratic factors `X² − γ_i` with
//! `γ_i = ζ^(2·BitRev7(i) + 1)` and `ζ = 17`, rather than into 256 linear ones.
//! An element in NTT form is therefore a vector of 128 pairs — the residues
//! `ŵ[2i] + ŵ[2i+1]·X = w mod (X² − γ_i)` — and [`NttKem`] carries that shape,
//! `[[u16; 2]; 128]`. `basemul` is 128 independent products of degree-1
//! polynomials modulo `X² − γ_i` (FIPS 203 Algorithm 12), not 256 scalar
//! products.
//!
//! The trait accommodates that shape unchanged: [`PolyRing::basemul`] is the
//! instance's own operation on the instance's own [`PolyRing::NttForm`], and
//! [`PolyRing::ntt_coeff`] reads entry `i` of that form for `i < N` whether an
//! entry is an evaluation (ML-DSA) or one coefficient of one residue (here).
//!
//! Like `mldsa_q`, this module is the opaque arithmetic leaf: it is gated out of
//! the hax extraction and exists so that the surface runs under rustc and its
//! tests compare it with the FIPS 203 specification crate.

// Indexed loops mirror the index-by-index statement of the algorithms.
#![allow(clippy::needless_range_loop)]

use crate::poly::{PolyRing, MODULUS_MLKEM};
use crate::Field;

const Q: u32 = MODULUS_MLKEM;

/// ζ = 17, a primitive 256th root of unity modulo q (FIPS 203 §4.3).
pub const ZETA: u16 = 17;

/// `128⁻¹ mod q` (FIPS 203 Algorithm 10): the transform has 7 layers, so the
/// inverse scales by `2^-7`, not by `n^-1`.
pub const INV_128: u16 = 3303;

/// The number of quadratic factors of `X^256 + 1` the incomplete transform
/// produces, and so the number of blocks of an element in NTT form.
pub const BLOCKS: usize = 128;

/// An element of `Z_q`, stored as its representative in `[0, q)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fq(pub u16);

impl Fq {
    /// The residue of `n` modulo q.
    pub fn new(n: u32) -> Self {
        Fq((n % Q) as u16)
    }

    fn pow_u32(self, mut e: u32) -> Self {
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
        Fq::new(self.0 as u32 + rhs.0 as u32)
    }
    fn sub(self, rhs: Self) -> Self {
        Fq::new(self.0 as u32 + Q - rhs.0 as u32)
    }
    fn mul(self, rhs: Self) -> Self {
        Fq::new(self.0 as u32 * rhs.0 as u32)
    }
    fn neg(self) -> Self {
        Fq::new(Q - self.0 as u32)
    }
    fn square(self) -> Self {
        self.mul(self)
    }
    fn double(self) -> Self {
        self.add(self)
    }
    fn inv(self) -> Self {
        // Fermat: a^(q−2).
        self.pow_u32(Q - 2)
    }
    fn pow(self, exp: &[u64]) -> Self {
        let mut acc = Fq(1);
        let mut j = exp.len();
        while j > 0 {
            j -= 1;
            let limb = exp[j];
            let mut bit = 64;
            while bit > 0 {
                bit -= 1;
                acc = acc.mul(acc);
                if (limb >> bit) & 1 == 1 {
                    acc = acc.mul(self);
                }
            }
        }
        acc
    }
    fn from_bytes(bytes: &[u8]) -> Self {
        let mut acc = 0u32;
        let mut i = bytes.len();
        while i > 0 {
            i -= 1;
            acc = (acc * 256 + bytes[i] as u32) % Q;
        }
        Fq(acc as u16)
    }
    fn to_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..2].copy_from_slice(&self.0.to_le_bytes());
        out
    }
}

/// BitRev7 (FIPS 203 §4.3): the reversal of the low seven bits, indexing the
/// 128 quadratic factors.
pub fn bit_rev_7(n: usize) -> usize {
    let mut r = 0usize;
    let mut x = n;
    for _ in 0..7 {
        r = (r << 1) | (x & 1);
        x >>= 1;
    }
    r
}

/// `ζ^BitRev7(k) mod q` (FIPS 203 Appendix A), the twiddle of butterfly group
/// `k`, for `1 <= k < 128`.
pub fn zeta_pow(k: usize) -> Fq {
    Fq(ZETA).pow_u32(bit_rev_7(k) as u32)
}

/// `γ_i = ζ^(2·BitRev7(i) + 1)`, the root of the `i`th quadratic factor
/// `X² − γ_i` of `X^256 + 1`, for `i < 128`.
pub fn gamma(i: usize) -> Fq {
    Fq(ZETA).pow_u32((2 * bit_rev_7(i) + 1) as u32)
}

/// An element of `Z_q[X]/(X^256 + 1)` in coefficient form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolyKem(pub [u16; 256]);

/// An element of the ring in NTT form: the 128 residues
/// `w mod (X² − γ_i)`, each a pair `[c0, c1]` standing for `c0 + c1·X`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NttKem(pub [[u16; 2]; BLOCKS]);

/// The 256 entries of an element in NTT form, block by block — the layout
/// FIPS 203 stores and encodes.
pub fn flatten(w: NttKem) -> [u16; 256] {
    let mut f = [0u16; 256];
    for i in 0..BLOCKS {
        f[2 * i] = w.0[i][0];
        f[2 * i + 1] = w.0[i][1];
    }
    f
}

/// The element in NTT form with the 256 entries `f`, read block by block.
pub fn unflatten(f: [u16; 256]) -> NttKem {
    let mut w = [[0u16; 2]; BLOCKS];
    for i in 0..BLOCKS {
        w[i][0] = f[2 * i];
        w[i][1] = f[2 * i + 1];
    }
    NttKem(w)
}

impl PolyRing for PolyKem {
    type Coeff = Fq;
    type NttForm = NttKem;
    const N: usize = 256;
    const ZERO: Self = PolyKem([0u16; 256]);
    const NTT_ZERO: NttKem = NttKem([[0u16; 2]; BLOCKS]);

    fn coeff(self, i: usize) -> Fq {
        Fq(self.0[i])
    }
    fn with_coeff(self, i: usize, c: Fq) -> Self {
        let mut w = self;
        w.0[i] = c.0;
        w
    }
    /// Entry `i` of the NTT form: coefficient `i mod 2` of residue `i / 2`.
    fn ntt_coeff(w: NttKem, i: usize) -> Fq {
        Fq(w.0[i >> 1][i & 1])
    }
    /// Entry replacement at the same address: coefficient `i mod 2` of residue
    /// `i / 2`, the step `Â` (FIPS 203 Algorithm 13) samples with.
    fn with_ntt_coeff(w: NttKem, i: usize, c: Fq) -> NttKem {
        let mut v = w;
        v.0[i >> 1][i & 1] = c.0;
        v
    }

    /// FIPS 203 Algorithm 9: seven layers, leaving the 128 residues
    /// `ŵ[2i] + ŵ[2i+1]·X = w mod (X² − γ_i)`.
    fn ntt(self) -> NttKem {
        let mut w = self.0;
        let mut k = 1usize;
        let mut len = 128usize;
        while len >= 2 {
            let mut start = 0usize;
            while start < 256 {
                let z = zeta_pow(k);
                k += 1;
                for j in start..start + len {
                    let t = z.mul(Fq(w[j + len]));
                    w[j + len] = Fq(w[j]).sub(t).0;
                    w[j] = Fq(w[j]).add(t).0;
                }
                start += 2 * len;
            }
            len >>= 1;
        }
        unflatten(w)
    }

    /// FIPS 203 Algorithm 10, closing with the factor `128⁻¹`.
    fn intt(w_hat: NttKem) -> Self {
        let mut w = flatten(w_hat);
        let mut k = 127usize;
        let mut len = 2usize;
        while len <= 128 {
            let mut start = 0usize;
            while start < 256 {
                let z = zeta_pow(k);
                k = k.wrapping_sub(1);
                for j in start..start + len {
                    let t = Fq(w[j]);
                    w[j] = t.add(Fq(w[j + len])).0;
                    w[j + len] = z.mul(Fq(w[j + len]).sub(t)).0;
                }
                start += 2 * len;
            }
            len <<= 1;
        }
        for i in 0..256 {
            w[i] = Fq(w[i]).mul(Fq(INV_128)).0;
        }
        PolyKem(w)
    }

    /// FIPS 203 Algorithms 11 and 12: 128 independent products of degree-1
    /// polynomials modulo `X² − γ_i`,
    /// `(a0 + a1·X)(b0 + b1·X) = (a0·b0 + a1·b1·γ_i) + (a0·b1 + a1·b0)·X`.
    fn basemul(a: NttKem, b: NttKem) -> NttKem {
        let mut w = [[0u16; 2]; BLOCKS];
        for i in 0..BLOCKS {
            let g = gamma(i);
            let (a0, a1) = (Fq(a.0[i][0]), Fq(a.0[i][1]));
            let (b0, b1) = (Fq(b.0[i][0]), Fq(b.0[i][1]));
            w[i][0] = a0.mul(b0).add(a1.mul(b1).mul(g)).0;
            w[i][1] = a0.mul(b1).add(a1.mul(b0)).0;
        }
        NttKem(w)
    }
    fn ntt_add(a: NttKem, b: NttKem) -> NttKem {
        let mut w = [[0u16; 2]; BLOCKS];
        for i in 0..BLOCKS {
            w[i][0] = Fq(a.0[i][0]).add(Fq(b.0[i][0])).0;
            w[i][1] = Fq(a.0[i][1]).add(Fq(b.0[i][1])).0;
        }
        NttKem(w)
    }
    fn ntt_sub(a: NttKem, b: NttKem) -> NttKem {
        let mut w = [[0u16; 2]; BLOCKS];
        for i in 0..BLOCKS {
            w[i][0] = Fq(a.0[i][0]).sub(Fq(b.0[i][0])).0;
            w[i][1] = Fq(a.0[i][1]).sub(Fq(b.0[i][1])).0;
        }
        NttKem(w)
    }
    fn poly_add(self, rhs: Self) -> Self {
        let mut w = [0u16; 256];
        for i in 0..256 {
            w[i] = Fq(self.0[i]).add(Fq(rhs.0[i])).0;
        }
        PolyKem(w)
    }
    fn poly_sub(self, rhs: Self) -> Self {
        let mut w = [0u16; 256];
        for i in 0..256 {
            w[i] = Fq(self.0[i]).sub(Fq(rhs.0[i])).0;
        }
        PolyKem(w)
    }
    fn poly_smul(self, c: Fq) -> Self {
        let mut w = [0u16; 256];
        for i in 0..256 {
            w[i] = c.mul(Fq(self.0[i])).0;
        }
        PolyKem(w)
    }
    fn ntt_mul(self, rhs: Self) -> Self {
        Self::intt(Self::basemul(self.ntt(), rhs.ntt()))
    }
}
