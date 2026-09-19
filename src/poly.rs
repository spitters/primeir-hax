//! The polynomial-ring op family of the prime-IR surface.
//!
//! [`PolyRing`] names the operations of the `polyDialect` of the CatCrypt
//! compiler (`SecureCompilation/VIR/PolyDialect.lean`, `PolyOp`): each method
//! carries the name of the dialect operation it denotes, so an extraction
//! recognises a call by trait and method name and the realisation stays an
//! opaque arithmetic leaf. As in the dialect, an element in coefficient form
//! (`polyC q n`, the type implementing the trait) and an element in NTT form
//! (`polyN q n`, [`PolyRing::NttForm`]) have different types.
//!
//! | method      | `PolyOp`   | type                         | meaning over `Z_q[X]/(X^n + 1)`        |
//! |-------------|------------|------------------------------|----------------------------------------|
//! | `ntt`       | `ntt`      | `polyC → polyN`              | coefficient form to NTT form           |
//! | `intt`      | `intt`     | `polyN → polyC`              | NTT form to coefficient form           |
//! | `basemul`   | `basemul`  | `polyN → polyN → polyN`      | product of two elements in NTT form    |
//! | `poly_add`  | `polyAdd`  | `polyC → polyC → polyC`      | sum                                    |
//! | `poly_sub`  | `polySub`  | `polyC → polyC → polyC`      | difference                             |
//! | `poly_smul` | `polySMul` | `polyC → polyC`              | product with a scalar                  |
//! | `ntt_mul`   | `nttMul`   | `polyC → polyC → polyC`      | product in the ring                    |
//! | `ntt_add`   | —          | `polyN → polyN → polyN`      | sum of two elements in NTT form        |
//!
//! `ntt_add` is AddNTT of FIPS 204 (Algorithm 44), which a matrix-vector product
//! in NTT form needs; `PolyOp` has no operation for it, and by linearity of the
//! transform it equals `ntt (poly_add (intt a) (intt b))`.
//!
//! The order of the NTT outputs is part of the meaning of `ntt`: a scheme that
//! samples elements directly in NTT form (ML-DSA's `ExpandA`, FIPS 204
//! Algorithm 32) observes it. An instance states its order; the ML-DSA instance
//! is `ŵ[i] = w(ζ^(2·BitRev8(i) + 1))` with `ζ = 1753` (FIPS 204 §7.5).

use crate::Field;

/// A ring `Z_q[X]/(X^n + 1)` with a number-theoretic transform, over the
/// coefficient field [`PolyRing::Coeff`]. `Self` is an element in coefficient
/// form.
pub trait PolyRing: Copy + Clone + PartialEq {
    /// The coefficient field `Z_q`.
    type Coeff: Field;

    /// An element in NTT form (`polyN q n`).
    type NttForm: Copy + Clone + PartialEq;

    /// The degree `n`.
    const N: usize;

    /// The zero polynomial.
    const ZERO: Self;

    /// Coefficient `i`, for `i < N`.
    fn coeff(self, i: usize) -> Self::Coeff;
    /// The polynomial with coefficient `i` replaced by `c`, for `i < N`.
    fn with_coeff(self, i: usize, c: Self::Coeff) -> Self;
    /// Entry `i` of an element in NTT form, for `i < N`.
    fn ntt_coeff(w: Self::NttForm, i: usize) -> Self::Coeff;

    /// `PolyOp.ntt`.
    fn ntt(self) -> Self::NttForm;
    /// `PolyOp.intt`.
    fn intt(w: Self::NttForm) -> Self;
    /// `PolyOp.basemul`: the product of two elements in NTT form.
    fn basemul(a: Self::NttForm, b: Self::NttForm) -> Self::NttForm;
    /// The sum of two elements in NTT form (FIPS 204 Algorithm 44).
    fn ntt_add(a: Self::NttForm, b: Self::NttForm) -> Self::NttForm;
    /// `PolyOp.polyAdd`.
    fn poly_add(self, rhs: Self) -> Self;
    /// `PolyOp.polySub`.
    fn poly_sub(self, rhs: Self) -> Self;
    /// `PolyOp.polySMul`.
    fn poly_smul(self, c: Self::Coeff) -> Self;
    /// `PolyOp.nttMul`: the product in `Z_q[X]/(X^n + 1)`.
    fn ntt_mul(self, rhs: Self) -> Self;
}

/// A generic caller of [`PolyRing::ntt_mul`], so that an extraction contains a
/// call site for the ring product. Not `cfg`-gated: the extraction must see it.
pub fn poly_mul_demo<R: PolyRing>(a: R, b: R) -> R {
    a.ntt_mul(b)
}

/// A generic caller of [`PolyRing::ntt`], [`PolyRing::basemul`],
/// [`PolyRing::intt`] and [`PolyRing::poly_add`]: one entry `a·s + e` of a
/// module-LWE sample with `a` given in NTT form, as ML-KEM and ML-DSA key
/// generation compute it.
pub fn mlwe_entry_demo<R: PolyRing>(a_hat: R::NttForm, s: R, e: R) -> R {
    R::intt(R::basemul(a_hat, s.ntt())).poly_add(e)
}

/// A generic caller of [`PolyRing::ntt_add`]: the inner product of two vectors
/// of length two in NTT form, the step of a matrix-vector product.
pub fn ntt_dot2_demo<R: PolyRing>(
    a0: R::NttForm,
    a1: R::NttForm,
    v0: R::NttForm,
    v1: R::NttForm,
) -> R::NttForm {
    R::ntt_add(R::basemul(a0, v0), R::basemul(a1, v1))
}

/// The modulus of ML-DSA (FIPS 204 Table 1), `q = 2^23 − 2^13 + 1`, as a source
/// constant on the extraction surface.
pub const MODULUS_MLDSA: u32 = 8380417;

/// Keeps [`MODULUS_MLDSA`] on the extraction surface.
pub fn modulus_mldsa() -> u32 {
    MODULUS_MLDSA
}
