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
//! | method            | `PolyOp`   | type                         | meaning over `Z_q[X]/(X^n + 1)`        |
//! |-------------------|------------|------------------------------|----------------------------------------|
//! | `ntt`             | `ntt`      | `polyC → polyN`              | coefficient form to NTT form           |
//! | `intt`            | `intt`     | `polyN → polyC`              | NTT form to coefficient form           |
//! | `basemul`         | `basemul`  | `polyN → polyN → polyN`      | product of two elements in NTT form    |
//! | `poly_add`        | `polyAdd`  | `polyC → polyC → polyC`      | sum                                    |
//! | `poly_sub`        | `polySub`  | `polyC → polyC → polyC`      | difference                             |
//! | `poly_smul`       | `polySMul` | `polyC → polyC`              | product with a scalar                  |
//! | `ntt_mul`         | `nttMul`   | `polyC → polyC → polyC`      | product in the ring                    |
//! | `ntt_add`         | —          | `polyN → polyN → polyN`      | sum of two elements in NTT form        |
//! | `ntt_sub`         | —          | `polyN → polyN → polyN`      | difference of two elements in NTT form |
//! | `ntt_coeff`       | —          | `polyN → usize → Coeff`      | entry of an element in NTT form        |
//! | `with_ntt_coeff`  | —          | `polyN → usize → Coeff → polyN` | entry replacement in NTT form       |
//!
//! `ntt_add` is AddNTT of FIPS 204 (Algorithm 44), which a matrix-vector product
//! in NTT form needs, and `ntt_sub` is the difference it pairs with, which the
//! residual `â ∘ ẑ − ĉ ∘ t̂` of ML-DSA verification (Algorithm 8 line 11) needs.
//! `PolyOp` has no operation for either, and by linearity of the transform they
//! equal `ntt (poly_add (intt a) (intt b))` and `ntt (poly_sub (intt a) (intt b))`.
//!
//! `NTT_ZERO` and `with_ntt_coeff` build an element of `polyN` directly, which a
//! scheme that samples in NTT form (ML-DSA's `ExpandA`, ML-KEM's `Â`) needs and
//! which make `ntt ∘ intt = id` statable on an arbitrary element of `polyN`.
//!
//! [`PolyRing`] states the laws all of these operations satisfy.
//!
//! The order in which the transform lists its outputs is **not** fixed by the
//! trait: it is part of the meaning of `ntt` at each instance, and a scheme that
//! samples elements directly in NTT form observes it. Each instance states its
//! own; see [`PolyRing`] §"What the trait leaves to the instance".
//!
//! Two instances live in this crate, both gated out of the extraction:
//! `mldsa_q` (`q = 8380417`, `n = 256`, the complete 8-layer transform of
//! FIPS 204 §7.5) and `mlkem_q` (`q = 3329`, `n = 256`, the incomplete 7-layer
//! transform of FIPS 203 §4.3). They differ in how far the transform splits
//! `X^n + 1`: ML-DSA's splits it into 256 linear factors, so `basemul` is 256
//! scalar products; ML-KEM's stops one layer early at 128 quadratic factors, so
//! `basemul` is 128 independent products of degree-1 polynomials. The trait
//! accommodates both because `basemul` is the instance's own operation on the
//! instance's own [`PolyRing::NttForm`].

use crate::Field;

/// A ring `Z_q[X]/(X^n + 1)` with a number-theoretic transform, over the
/// coefficient field [`PolyRing::Coeff`]. `Self` is an element in coefficient
/// form.
///
/// # The contract
///
/// Write `q` for the modulus of `Coeff`, `n` for [`PolyRing::N`], `R` for
/// `Z_q[X]/(X^n + 1)` and `a_i` for `a.coeff(i)`. An implementor must satisfy,
/// for all `a`, `b` of type `Self`, all `w`, `v` of type `Self::NttForm`, all
/// `c : Coeff` and all `i < n`:
///
/// 1. **The transform is a bijection.** `Self::intt(a.ntt()) == a` and
///    `Self::intt(w).ntt() == w`. Coefficient form and NTT form are two
///    representations of the same element of `R`.
/// 2. **`ntt_mul` is the product of `R`** — the negacyclic convolution
///    `(a · b)_k = Σ_{i+j=k} a_i·b_j − Σ_{i+j=k+n} a_i·b_j`, reading `X^n = −1`.
///    It is commutative and associative, distributes over `poly_add`, and has
///    the constant polynomial `1` as unit.
/// 3. **`basemul` is that product transported along the transform**:
///    `Self::basemul(a.ntt(), b.ntt()) == a.ntt_mul(b).ntt()`, equivalently
///    `Self::intt(Self::basemul(a.ntt(), b.ntt())) == a.ntt_mul(b)`. It is the
///    multiplication of `polyN` that makes `ntt` a ring isomorphism. Whether
///    that multiplication is entrywise in `Coeff` or blockwise over larger
///    factors depends on how far the transform splits `X^n + 1`, and is stated
///    by the instance, not here.
/// 4. **`ntt_add` and `ntt_sub` are the sum and the difference transported
///    along the transform**: `Self::ntt_add(a.ntt(), b.ntt()) ==
///    a.poly_add(b).ntt()` and `Self::ntt_sub(a.ntt(), b.ntt()) ==
///    a.poly_sub(b).ntt()`. Equivalently `Self::intt(Self::ntt_add(w, v)) ==
///    Self::intt(w).poly_add(Self::intt(v))` and
///    `Self::intt(Self::ntt_sub(w, v)) == Self::intt(w).poly_sub(Self::intt(v))`.
///    Together with 3 this says `ntt` is a ring homomorphism.
/// 5. **`poly_add`, `poly_sub` and `poly_smul` are coefficient-wise**:
///    `a.poly_add(b).coeff(i) == a_i.add(b_i)`, `a.poly_sub(b).coeff(i) ==
///    a_i.sub(b_i)` and `a.poly_smul(c).coeff(i) == c.mul(a_i)`.
/// 6. **`ZERO`, `coeff` and `with_coeff` present the coefficient vector**:
///    `Self::ZERO.coeff(i) == Coeff::ZERO`, `a.with_coeff(i, c).coeff(i) == c`,
///    `a.with_coeff(i, c).coeff(j) == a_j` for `j != i`, and two elements with
///    equal coefficients are equal. `Self::ZERO` is the unit of `poly_add`.
/// 7. **`ntt_coeff` presents the NTT-form vector** in the same way: entry `i`
///    of `w` for `i < n`, with `Self::intt(w).ntt() == w` recovering the whole
///    of it. The entries are elements of `Coeff` in both the complete and the
///    incomplete case; what an entry *means* — an evaluation, or one
///    coefficient of one of the `n/d` factors — is stated by the instance.
/// 8. **`NTT_ZERO` and `with_ntt_coeff` build an element of `polyN` entry by
///    entry**, without going through `ntt`, as a scheme that samples a matrix
///    directly in NTT form does (ML-DSA's `ExpandA`, FIPS 204 Algorithm 32;
///    ML-KEM's `Â`, FIPS 203 Algorithm 13). For `i != j`, both below `n`:
///    `Self::ntt_coeff(Self::NTT_ZERO, i) == Coeff::ZERO` and
///    `Self::NTT_ZERO == Self::ZERO.ntt()`;
///    `Self::ntt_coeff(Self::with_ntt_coeff(w, i, c), i) == c`;
///    `Self::ntt_coeff(Self::with_ntt_coeff(w, i, c), j) == Self::ntt_coeff(w, j)`;
///    and every element of `NttForm` is reachable — filling all `n` entries of
///    `NTT_ZERO` with the entries of `w` yields `w`. Reachability is what makes
///    the second half of law 1 a statement about an arbitrary element of
///    `polyN`, not only about one in the image of `ntt`.
///
/// `crate::poly_laws` checks every one of these on pseudorandom inputs, for any
/// implementor.
///
/// # What the trait leaves to the instance
///
/// **The evaluation ordering of `ntt`.** The laws above are invariant under
/// permuting the entries of `polyN` and under changing which root of unity the
/// transform uses, so they do not pin the transform down; a scheme that samples
/// an element directly in NTT form (ML-DSA's `ExpandA`, FIPS 204 Algorithm 32;
/// ML-KEM's `Â`, FIPS 203 Algorithm 13) observes the choice, so it cannot be
/// left open. An instance states it:
///
/// * `mldsa_q`: `ŵ[i] = w(ζ^(2·BitRev8(i) + 1))` with `ζ = 1753`
///   (FIPS 204 §7.5) — the transform is complete, and each entry is an
///   evaluation at one of the 256 primitive 512th roots of unity.
/// * `mlkem_q`: `ŵ[2i] + ŵ[2i+1]·X = w mod (X² − ζ^(2·BitRev7(i) + 1))` with
///   `ζ = 17` (FIPS 203 §4.3) — the transform stops one layer early, and a pair
///   of entries is the residue of `w` modulo one of the 128 quadratic factors.
///
/// **The shape of `basemul`**, for the same reason: 256 products in `Coeff` at
/// `mldsa_q` (FIPS 204 Algorithm 45), 128 products of degree-1 polynomials
/// modulo `X² − γ_i` at `mlkem_q` (FIPS 203 Algorithm 12).
pub trait PolyRing: Copy + Clone + PartialEq {
    /// The coefficient field `Z_q`.
    type Coeff: Field;

    /// An element in NTT form (`polyN q n`).
    type NttForm: Copy + Clone + PartialEq;

    /// The degree `n`.
    const N: usize;

    /// The zero polynomial.
    const ZERO: Self;

    /// The zero of `polyN` — the transform of [`PolyRing::ZERO`].
    const NTT_ZERO: Self::NttForm;

    /// Coefficient `i`, for `i < N`.
    fn coeff(self, i: usize) -> Self::Coeff;
    /// The polynomial with coefficient `i` replaced by `c`, for `i < N`.
    fn with_coeff(self, i: usize, c: Self::Coeff) -> Self;
    /// Entry `i` of an element in NTT form, for `i < N`.
    fn ntt_coeff(w: Self::NttForm, i: usize) -> Self::Coeff;
    /// The element of `polyN` with entry `i` replaced by `c`, for `i < N`.
    fn with_ntt_coeff(w: Self::NttForm, i: usize, c: Self::Coeff) -> Self::NttForm;

    /// `PolyOp.ntt`.
    fn ntt(self) -> Self::NttForm;
    /// `PolyOp.intt`.
    fn intt(w: Self::NttForm) -> Self;
    /// `PolyOp.basemul`: the product of two elements in NTT form.
    fn basemul(a: Self::NttForm, b: Self::NttForm) -> Self::NttForm;
    /// The sum of two elements in NTT form (FIPS 204 Algorithm 44).
    fn ntt_add(a: Self::NttForm, b: Self::NttForm) -> Self::NttForm;
    /// The difference of two elements in NTT form.
    fn ntt_sub(a: Self::NttForm, b: Self::NttForm) -> Self::NttForm;
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

/// A generic caller of [`PolyRing::ntt_sub`]: one entry of the residual
/// `â ∘ ẑ − ĉ ∘ t̂` that ML-DSA verification forms in NTT form (FIPS 204
/// Algorithm 8 line 11).
pub fn ntt_residual_demo<R: PolyRing>(
    a: R::NttForm,
    z: R::NttForm,
    c: R::NttForm,
    t: R::NttForm,
) -> R::NttForm {
    R::ntt_sub(R::basemul(a, z), R::basemul(c, t))
}

/// A generic caller of [`PolyRing::with_ntt_coeff`]: the element of `polyN`
/// whose entries are the entries of `w` with entry `i` replaced by `c`, the
/// step by which a sampler in NTT form builds one from
/// [`PolyRing::NTT_ZERO`].
pub fn ntt_sample_demo<R: PolyRing>(w: R::NttForm, i: usize, c: R::Coeff) -> R::NttForm {
    R::with_ntt_coeff(w, i, c)
}

/// The modulus of ML-DSA (FIPS 204 Table 1), `q = 2^23 − 2^13 + 1`, as a source
/// constant on the extraction surface.
pub const MODULUS_MLDSA: u32 = 8380417;

/// Keeps [`MODULUS_MLDSA`] on the extraction surface.
pub fn modulus_mldsa() -> u32 {
    MODULUS_MLDSA
}

/// The modulus of ML-KEM (FIPS 203 §4), `q = 3329 = 13·2^8 + 1`, as a source
/// constant on the extraction surface.
pub const MODULUS_MLKEM: u32 = 3329;

/// Keeps [`MODULUS_MLKEM`] on the extraction surface.
pub fn modulus_mlkem() -> u32 {
    MODULUS_MLKEM
}
