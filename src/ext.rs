//! The extension-field op family of the prime-IR surface.
//!
//! [`ExtField`] names the operations of a compiler's tower dialect
//! (`towerDialect`, `TowerOp`) at one level of a tower of extensions of a
//! prime field, such as `Fp2`, `Fp6` and `Fp12` of a pairing-friendly curve.
//! As for the other families, each method carries the name of the operation
//! it denotes, so an extraction recognises a call by trait and method name,
//! and the realisation stays an opaque arithmetic leaf.
//!
//! | method              | `TowerOp`         | meaning                                         |
//! |---------------------|-------------------|-------------------------------------------------|
//! | `add`/`sub`/`neg`   | `add`/`sub`/`neg` | the additive group                              |
//! | `mul`/`square`      | `mul`/`square`    | the product, and `a ↦ a·a`                      |
//! | `inv`               | —                 | the inverse of a nonzero element                |
//! | `conj`              | `frobenius2` at `Fp2` | `frobenius(DEGREE / 2)`                     |
//! | `frobenius`         | —                 | `a ↦ a^(p^k)`                                   |
//! | `mul_by_nonresidue` | `mulByNonResidue` | the product with [`ExtField::NONRESIDUE`]       |
//! | `lift`              | `lift`            | the embedding of the level below                |
//!
//! `ExtField` is not a subtrait of [`crate::Field`]: a level is named by its
//! own trait, so that a call of `ExtField::mul` and a call of `Field::mul`
//! have different qualified heads, and a type may implement both without a
//! call site becoming ambiguous for the extraction. The level below is
//! [`ExtField::Base`], which is a prime field (`Fp` under `Fp2`) or another
//! level (`Fp2` under `Fp6`).
//!
//! The reference instance is `crate::ext_ref` (the tower over `2^31 − 1`),
//! gated out of the extraction.

/// One level of a tower of extensions of the prime field `GF(p)`.
///
/// # The contract
///
/// Write `p` for the characteristic, whose limbs are
/// [`ExtField::MODULUS_LE`], and `d` for [`ExtField::DEGREE`], the degree of
/// `Self` over `GF(p)`, which is even. An implementor must satisfy, for all
/// `a`, `b`, `c` and all `i`, `j`:
///
/// 1. `ZERO`, `ONE`, `add`, `sub`, `neg` and `mul` make `Self` a field;
///    `square(a) == a.mul(a)`, and `a.mul(a.inv()) == ONE` for `a != ZERO`.
/// 2. `frobenius(a, 1)` is `a^p`, `frobenius(a, i)` is `frobenius` applied
///    `i` times, and `frobenius(a, d) == a`. Each `frobenius(·, i)` is a ring
///    homomorphism.
/// 3. `conj(a) == frobenius(a, d / 2)`: the automorphism of order 2 over the
///    subfield of index 2. At `Fp2` it is `a + b·u ↦ a − b·u`, at `Fp12 =
///    Fp6[w]` it is `a + b·w ↦ a − b·w`.
/// 4. `mul_by_nonresidue(a) == a.mul(NONRESIDUE)`. `NONRESIDUE` is the
///    element the next level adjoins a root of: `ξ` at `Fp2` (`Fp6 =
///    Fp2[v]/(v³ − ξ)`), `v` at `Fp6`, `w` at `Fp12`.
/// 5. `lift` is an injective ring homomorphism from `Base`.
///
/// `crate::laws` states 1–4 as Boolean functions; the tests of the reference
/// instance assert them and assert 5 directly.
pub trait ExtField: Copy + Clone + PartialEq {
    /// The level below: a prime field or another level of the tower.
    type Base: Copy + Clone + PartialEq;

    /// The characteristic `p`, as little-endian `u64` limbs whose last limb is
    /// nonzero.
    const MODULUS_LE: &'static [u64];
    /// The degree of `Self` over `GF(p)` (2 at `Fp2`, 6 at `Fp6`, 12 at
    /// `Fp12`).
    const DEGREE: usize;
    /// The additive identity.
    const ZERO: Self;
    /// The multiplicative identity.
    const ONE: Self;
    /// The element [`ExtField::mul_by_nonresidue`] multiplies by.
    const NONRESIDUE: Self;

    /// The embedding of the level below. `TowerOp.lift`.
    fn lift(b: Self::Base) -> Self;
    /// Addition. `TowerOp.add`.
    fn add(self, rhs: Self) -> Self;
    /// Subtraction. `TowerOp.sub`.
    fn sub(self, rhs: Self) -> Self;
    /// Negation. `TowerOp.neg`.
    fn neg(self) -> Self;
    /// Multiplication. `TowerOp.mul`.
    fn mul(self, rhs: Self) -> Self;
    /// Squaring. `TowerOp.square`.
    fn square(self) -> Self;
    /// The inverse of a nonzero element; `inv(ZERO)` is unspecified.
    fn inv(self) -> Self;
    /// `frobenius(DEGREE / 2)`. `TowerOp.frobenius2` at `Fp2`.
    fn conj(self) -> Self;
    /// The `power`-th iterate of the Frobenius map, `a ↦ a^(p^power)`.
    fn frobenius(self, power: usize) -> Self;
    /// The product with [`ExtField::NONRESIDUE`]. `TowerOp.mulByNonResidue`.
    fn mul_by_nonresidue(self) -> Self;
}

/// A generic caller of [`ExtField::mul`] and [`ExtField::square`]: `a·b + a²`,
/// so that an extraction contains a call site for each. Not `cfg`-gated: the
/// extraction must see it.
pub fn ext_mul_demo<E: ExtField>(a: E, b: E) -> E {
    a.mul(b).add(a.square())
}

/// A generic caller of [`ExtField::conj`] and [`ExtField::mul`]: the norm-like
/// product `a·conj(a)`, which in the final exponentiation of a pairing
/// computes `f^(p^6 + 1)` at `Fp12`.
pub fn ext_conj_demo<E: ExtField>(a: E) -> E {
    a.mul(a.conj())
}

/// A generic caller of [`ExtField::frobenius`]: `a^(p^k)·a`.
pub fn ext_frobenius_demo<E: ExtField>(a: E, k: usize) -> E {
    a.frobenius(k).mul(a)
}

/// A generic caller of [`ExtField::mul_by_nonresidue`] and [`ExtField::lift`]:
/// `NONRESIDUE·a + lift(b)`.
pub fn ext_mul_by_nonresidue_demo<E: ExtField>(a: E, b: E::Base) -> E {
    a.mul_by_nonresidue().add(E::lift(b))
}
