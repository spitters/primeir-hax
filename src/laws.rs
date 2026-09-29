//! The algebraic laws of the prime-IR traits, one Boolean function per law.
//!
//! Each function states one law of [`Field`], [`ModArith`], [`EcGroup`],
//! [`CtField`], [`SqrtRatio`] or [`PolyRing`] at the arguments it is given and
//! returns whether the law holds there. The same function serves two readers:
//!
//! * under rustc, the test suites ([`crate::poly_laws`], `tests/kat.rs`,
//!   `tests/ct_properties.rs` and the tests of the instances) assert it on
//!   sample inputs;
//! * under hax, the module is on the extraction surface, so the extraction
//!   carries the definition of each law, and a statement over an instance is
//!   `∀ x, law x = true`.
//!
//! The functions return `bool`, not `hax_lib::Prop`, because a `Prop` has no
//! value under rustc. A law quantified over an index takes the index as an
//! argument and holds vacuously outside the range the law is stated for, so
//! that the function is total; the test supplies the quantifier by iterating.
//! A law whose trait documentation states it only for some arguments (the
//! inverse for a nonzero element, `sqrt_ratio` for a nonzero denominator)
//! holds vacuously at the others.

use crate::ct::CtField;
use crate::poly::PolyRing;
use crate::sqrt::SqrtRatio;
use crate::{EcGroup, Field, ModArith};

// --- Field ------------------------------------------------------------------

/// Associativity of addition: `(a + b) + c = a + (b + c)`.
pub fn add_assoc_law<F: Field>(a: F, b: F, c: F) -> bool {
    a.add(b).add(c) == a.add(b.add(c))
}

/// Commutativity of addition: `a + b = b + a`.
pub fn add_comm_law<F: Field>(a: F, b: F) -> bool {
    a.add(b) == b.add(a)
}

/// `ZERO` is the unit of addition: `a + 0 = a`.
pub fn add_zero_law<F: Field>(a: F) -> bool {
    a.add(F::ZERO) == a
}

/// `neg` is the additive inverse: `a + (−a) = 0`.
pub fn add_neg_law<F: Field>(a: F) -> bool {
    a.add(a.neg()) == F::ZERO
}

/// The difference of an element with itself is zero: `a − a = 0`.
pub fn sub_self_law<F: Field>(a: F) -> bool {
    a.sub(a) == F::ZERO
}

/// Associativity of multiplication: `(a·b)·c = a·(b·c)`.
pub fn mul_assoc_law<F: Field>(a: F, b: F, c: F) -> bool {
    a.mul(b).mul(c) == a.mul(b.mul(c))
}

/// Commutativity of multiplication: `a·b = b·a`.
pub fn mul_comm_law<F: Field>(a: F, b: F) -> bool {
    a.mul(b) == b.mul(a)
}

/// `ONE` is the unit of multiplication: `a·1 = a`.
pub fn mul_one_law<F: Field>(a: F) -> bool {
    a.mul(F::ONE) == a
}

/// `inv` is the multiplicative inverse of a nonzero element: `a·a⁻¹ = 1` for
/// `a ≠ 0`. `inv(ZERO)` is unspecified ([`Field::inv`]), so the law holds at
/// `ZERO`.
pub fn mul_inv_law<F: Field>(a: F) -> bool {
    if a == F::ZERO {
        true
    } else {
        a.mul(a.inv()) == F::ONE
    }
}

/// Distributivity of multiplication over addition: `a·(b + c) = a·b + a·c`.
pub fn distrib_law<F: Field>(a: F, b: F, c: F) -> bool {
    a.mul(b.add(c)) == a.mul(b).add(a.mul(c))
}

/// `square` is `a ↦ a·a` ([`Field::square`]).
pub fn square_law<F: Field>(a: F) -> bool {
    a.square() == a.mul(a)
}

/// `double` is `a ↦ a + a` ([`Field::double`]).
pub fn double_law<F: Field>(a: F) -> bool {
    a.double() == a.add(a)
}

// --- ModArith ---------------------------------------------------------------

/// `from_mont` inverts `to_mont`: `from_mont(to_mont(a)) = a` (the contract of
/// [`ModArith`]).
pub fn mont_roundtrip_law<F: ModArith>(a: F) -> bool {
    a.to_mont().from_mont() == a
}

/// `mont_mul` is the product in the Montgomery domain:
/// `mont_mul(to_mont(a), to_mont(b)) = to_mont(a·b)` (the contract of
/// [`ModArith`]).
pub fn mont_mul_law<F: ModArith>(a: F, b: F) -> bool {
    a.to_mont().mont_mul(b.to_mont()) == a.mul(b).to_mont()
}

// --- EcGroup ----------------------------------------------------------------

/// `IDENTITY` is the two-sided unit of the group law: `P + O = P` and
/// `O + P = P`.
pub fn point_add_identity_law<G: EcGroup>(p: G) -> bool {
    p.point_add(G::IDENTITY) == p && G::IDENTITY.point_add(p) == p
}

/// `point_double` is `P ↦ 2P = P + P` ([`EcGroup::point_double`]).
pub fn point_double_law<G: EcGroup>(p: G) -> bool {
    p.point_double() == p.point_add(p)
}

// --- CtField ----------------------------------------------------------------

/// CT_SELECT picks its second argument under condition `1` and its third under
/// condition `0` ([`CtField::ct_select`]).
pub fn ct_select_law<F: CtField>(a: F, b: F) -> bool {
    F::ct_select(1, a, b) == a && F::ct_select(0, a, b) == b
}

/// CT_EQ is `1` on equal elements and `0` on distinct ones
/// ([`CtField::ct_eq`]).
pub fn ct_eq_law<F: CtField>(a: F, b: F) -> bool {
    if a == b {
        a.ct_eq(b) == 1
    } else {
        a.ct_eq(b) == 0
    }
}

/// `is_zero(a) = ct_eq(a, ZERO)` ([`CtField::is_zero`]).
pub fn is_zero_law<F: CtField>(a: F) -> bool {
    a.is_zero() == a.ct_eq(F::ZERO)
}

/// IS_NEGATIVE is a truth value, `0` or `1` ([`CtField::is_negative`]).
pub fn is_negative_bit_law<F: CtField>(a: F) -> bool {
    a.is_negative() <= 1
}

/// CT_ABS is `−a` when `a` is negative and `a` otherwise
/// ([`CtField::ct_abs`]).
pub fn ct_abs_law<F: CtField>(a: F) -> bool {
    if a.is_negative() == 1 {
        a.ct_abs() == a.neg()
    } else {
        a.ct_abs() == a
    }
}

// --- SqrtRatio --------------------------------------------------------------

/// `sqrt_ratio(u, v)` for `v ≠ 0` (RFC 9380, Appendix F.2.1): the flag is `1`
/// and `y²·v = u`, or the flag is `0` and `y²·v = Z·u`
/// ([`SqrtRatio::sqrt_ratio`]). The law holds at `v = 0`, where the operation
/// is not specified.
pub fn sqrt_ratio_law<F: SqrtRatio>(u: F, v: F) -> bool {
    if v == F::ZERO {
        true
    } else {
        let (is_square, y) = F::sqrt_ratio(u, v);
        let lhs = y.square().mul(v);
        if is_square == 1 {
            lhs == u
        } else if is_square == 0 {
            lhs == F::Z.mul(u)
        } else {
            false
        }
    }
}

// --- PolyRing ---------------------------------------------------------------
//
// The numbers refer to the laws of the contract of [`PolyRing`].

/// The negacyclic product of `Z_q[X]/(X^n + 1)` computed coefficient by
/// coefficient from the definition,
/// `(a·b)_k = Σ_{i+j=k} a_i·b_j − Σ_{i+j=k+n} a_i·b_j`.
/// [`ntt_mul_negacyclic_law`] states that [`PolyRing::ntt_mul`] equals it.
pub fn schoolbook_negacyclic<R: PolyRing>(a: R, b: R) -> R {
    let mut out = R::ZERO;
    for k in 0..R::N {
        let mut acc = <R::Coeff as Field>::ZERO;
        for i in 0..(k + 1) {
            acc = acc.add(a.coeff(i).mul(b.coeff(k - i)));
        }
        for i in (k + 1)..R::N {
            acc = acc.sub(a.coeff(i).mul(b.coeff(k + R::N - i)));
        }
        out = out.with_coeff(k, acc);
    }
    out
}

/// The constant polynomial `c`.
fn constant<R: PolyRing>(c: R::Coeff) -> R {
    R::ZERO.with_coeff(0, c)
}

/// Law 1, first half: `intt ∘ ntt = id`.
pub fn intt_ntt_law<R: PolyRing>(a: R) -> bool {
    R::intt(a.ntt()) == a
}

/// Law 1, second half: `ntt ∘ intt = id` on `polyN`.
pub fn ntt_intt_law<R: PolyRing>(w: R::NttForm) -> bool {
    R::intt(w).ntt() == w
}

/// Law 2: `ntt_mul` is the negacyclic convolution [`schoolbook_negacyclic`].
pub fn ntt_mul_negacyclic_law<R: PolyRing>(a: R, b: R) -> bool {
    a.ntt_mul(b) == schoolbook_negacyclic(a, b)
}

/// Law 2: `ntt_mul` is commutative.
pub fn ntt_mul_comm_law<R: PolyRing>(a: R, b: R) -> bool {
    a.ntt_mul(b) == b.ntt_mul(a)
}

/// Law 2: `ntt_mul` is associative.
pub fn ntt_mul_assoc_law<R: PolyRing>(a: R, b: R, c: R) -> bool {
    a.ntt_mul(b).ntt_mul(c) == a.ntt_mul(b.ntt_mul(c))
}

/// Law 2: `ntt_mul` distributes over `poly_add`.
pub fn ntt_mul_distrib_law<R: PolyRing>(a: R, b: R, c: R) -> bool {
    a.ntt_mul(b.poly_add(c)) == a.ntt_mul(b).poly_add(a.ntt_mul(c))
}

/// Law 2: the constant polynomial `1` is the unit of `ntt_mul`.
pub fn ntt_mul_one_law<R: PolyRing>(a: R) -> bool {
    a.ntt_mul(constant::<R>(<R::Coeff as Field>::ONE)) == a
}

/// Law 2: `ZERO` is absorbing for `ntt_mul`.
pub fn ntt_mul_zero_law<R: PolyRing>(a: R) -> bool {
    a.ntt_mul(R::ZERO) == R::ZERO
}

/// Law 2: `ntt_mul` commutes with the scalar product,
/// `a·(s·b) = s·(a·b)`.
pub fn ntt_mul_smul_law<R: PolyRing>(a: R, b: R, s: R::Coeff) -> bool {
    a.ntt_mul(b.poly_smul(s)) == a.ntt_mul(b).poly_smul(s)
}

/// Law 2: the quotient is by `X^n + 1`, that is `X^(n−1)·X = −1`, for `n > 1`.
pub fn negacyclic_wrap_law<R: PolyRing>() -> bool {
    if R::N > 1 {
        let one = <R::Coeff as Field>::ONE;
        let x_top = R::ZERO.with_coeff(R::N - 1, one);
        let x = R::ZERO.with_coeff(1, one);
        let minus_one = constant::<R>(<R::Coeff as Field>::ZERO.sub(one));
        x_top.ntt_mul(x) == minus_one
    } else {
        true
    }
}

/// Law 3: `basemul` is the ring product transported along the transform,
/// `basemul(ntt a, ntt b) = ntt(a·b)`.
pub fn basemul_law<R: PolyRing>(a: R, b: R) -> bool {
    R::basemul(a.ntt(), b.ntt()) == a.ntt_mul(b).ntt()
}

/// Law 3, in the other direction: `intt(basemul(ntt a, ntt b)) = a·b`.
pub fn intt_basemul_law<R: PolyRing>(a: R, b: R) -> bool {
    R::intt(R::basemul(a.ntt(), b.ntt())) == a.ntt_mul(b)
}

/// Law 3: `basemul` is commutative.
pub fn basemul_comm_law<R: PolyRing>(w: R::NttForm, v: R::NttForm) -> bool {
    R::basemul(w, v) == R::basemul(v, w)
}

/// Law 3: the transform of `ZERO` is absorbing for `basemul`.
pub fn basemul_zero_law<R: PolyRing>(w: R::NttForm) -> bool {
    R::basemul(w, R::ZERO.ntt()) == R::ZERO.ntt()
}

/// Law 4: `ntt_add` is the sum transported along the transform,
/// `ntt_add(ntt a, ntt b) = ntt(a + b)`.
pub fn ntt_add_law<R: PolyRing>(a: R, b: R) -> bool {
    R::ntt_add(a.ntt(), b.ntt()) == a.poly_add(b).ntt()
}

/// Law 4, in the other direction: `intt(ntt_add(ntt a, ntt b)) = a + b`.
pub fn intt_ntt_add_law<R: PolyRing>(a: R, b: R) -> bool {
    R::intt(R::ntt_add(a.ntt(), b.ntt())) == a.poly_add(b)
}

/// Law 4: `ntt_add` is entry-wise, for `i < N`.
pub fn ntt_add_entry_law<R: PolyRing>(w: R::NttForm, v: R::NttForm, i: usize) -> bool {
    if i < R::N {
        R::ntt_coeff(R::ntt_add(w, v), i) == R::ntt_coeff(w, i).add(R::ntt_coeff(v, i))
    } else {
        true
    }
}

/// Law 4: `ntt_sub` is the difference transported along the transform,
/// `ntt_sub(ntt a, ntt b) = ntt(a − b)`.
pub fn ntt_sub_law<R: PolyRing>(a: R, b: R) -> bool {
    R::ntt_sub(a.ntt(), b.ntt()) == a.poly_sub(b).ntt()
}

/// Law 4, in the other direction: `intt(ntt_sub(ntt a, ntt b)) = a − b`.
pub fn intt_ntt_sub_law<R: PolyRing>(a: R, b: R) -> bool {
    R::intt(R::ntt_sub(a.ntt(), b.ntt())) == a.poly_sub(b)
}

/// Law 4: `ntt_sub` is entry-wise, for `i < N`.
pub fn ntt_sub_entry_law<R: PolyRing>(w: R::NttForm, v: R::NttForm, i: usize) -> bool {
    if i < R::N {
        R::ntt_coeff(R::ntt_sub(w, v), i) == R::ntt_coeff(w, i).sub(R::ntt_coeff(v, i))
    } else {
        true
    }
}

/// Law 4: the difference in NTT form of an element with itself is the
/// transform of `ZERO`.
pub fn ntt_sub_self_law<R: PolyRing>(w: R::NttForm) -> bool {
    R::ntt_sub(w, w) == R::ZERO.ntt()
}

/// Law 4: `ntt_sub` inverts `ntt_add`, `(w − v) + v = w` in NTT form.
pub fn ntt_sub_add_law<R: PolyRing>(w: R::NttForm, v: R::NttForm) -> bool {
    R::ntt_add(R::ntt_sub(w, v), v) == w
}

/// Law 5: `poly_add` is coefficient-wise, for `i < N`.
pub fn poly_add_coeff_law<R: PolyRing>(a: R, b: R, i: usize) -> bool {
    if i < R::N {
        a.poly_add(b).coeff(i) == a.coeff(i).add(b.coeff(i))
    } else {
        true
    }
}

/// Law 5: `poly_sub` is coefficient-wise, for `i < N`.
pub fn poly_sub_coeff_law<R: PolyRing>(a: R, b: R, i: usize) -> bool {
    if i < R::N {
        a.poly_sub(b).coeff(i) == a.coeff(i).sub(b.coeff(i))
    } else {
        true
    }
}

/// Law 5: `poly_smul` is coefficient-wise, for `i < N`.
pub fn poly_smul_coeff_law<R: PolyRing>(a: R, c: R::Coeff, i: usize) -> bool {
    if i < R::N {
        a.poly_smul(c).coeff(i) == c.mul(a.coeff(i))
    } else {
        true
    }
}

/// Law 5: the difference of an element with itself is `ZERO`.
pub fn poly_sub_self_law<R: PolyRing>(a: R) -> bool {
    a.poly_sub(a) == R::ZERO
}

/// Law 5: the scalar product by `ONE` is the identity.
pub fn poly_smul_one_law<R: PolyRing>(a: R) -> bool {
    a.poly_smul(<R::Coeff as Field>::ONE) == a
}

/// Law 6: every coefficient of `ZERO` is zero, for `i < N`.
pub fn zero_coeff_law<R: PolyRing>(i: usize) -> bool {
    if i < R::N {
        R::ZERO.coeff(i) == <R::Coeff as Field>::ZERO
    } else {
        true
    }
}

/// Law 6: `with_coeff(i, c)` sets coefficient `i` to `c`, for `i < N`.
pub fn with_coeff_same_law<R: PolyRing>(a: R, i: usize, c: R::Coeff) -> bool {
    if i < R::N {
        a.with_coeff(i, c).coeff(i) == c
    } else {
        true
    }
}

/// Law 6: `with_coeff(i, c)` leaves coefficient `j` unchanged, for `i ≠ j`,
/// both below `N`.
pub fn with_coeff_other_law<R: PolyRing>(a: R, i: usize, c: R::Coeff, j: usize) -> bool {
    if i < R::N && j < R::N && i != j {
        a.with_coeff(i, c).coeff(j) == a.coeff(j)
    } else {
        true
    }
}

/// Law 6: an element is determined by its coefficients: writing the `N`
/// coefficients of `a` into `ZERO` yields `a`.
pub fn coeff_ext_law<R: PolyRing>(a: R) -> bool {
    let mut rebuilt = R::ZERO;
    for j in 0..R::N {
        rebuilt = rebuilt.with_coeff(j, a.coeff(j));
    }
    rebuilt == a
}

/// Law 6: `ZERO` is the unit of `poly_add`.
pub fn poly_add_zero_law<R: PolyRing>(a: R) -> bool {
    a.poly_add(R::ZERO) == a
}

/// Law 8: `NTT_ZERO` is the transform of `ZERO`.
pub fn ntt_zero_law<R: PolyRing>() -> bool {
    R::NTT_ZERO == R::ZERO.ntt()
}

/// Law 8: every entry of `NTT_ZERO` is zero, for `i < N`.
pub fn ntt_zero_coeff_law<R: PolyRing>(i: usize) -> bool {
    if i < R::N {
        R::ntt_coeff(R::NTT_ZERO, i) == <R::Coeff as Field>::ZERO
    } else {
        true
    }
}

/// Law 8: `with_ntt_coeff(w, i, c)` sets entry `i` to `c`, for `i < N`.
pub fn with_ntt_coeff_same_law<R: PolyRing>(w: R::NttForm, i: usize, c: R::Coeff) -> bool {
    if i < R::N {
        R::ntt_coeff(R::with_ntt_coeff(w, i, c), i) == c
    } else {
        true
    }
}

/// Law 8: `with_ntt_coeff(w, i, c)` leaves entry `j` unchanged, for `i ≠ j`,
/// both below `N`.
pub fn with_ntt_coeff_other_law<R: PolyRing>(
    w: R::NttForm,
    i: usize,
    c: R::Coeff,
    j: usize,
) -> bool {
    if i < R::N && j < R::N && i != j {
        R::ntt_coeff(R::with_ntt_coeff(w, i, c), j) == R::ntt_coeff(w, j)
    } else {
        true
    }
}

/// Law 8: every element of `polyN` is reachable: writing the `N` entries of
/// `w` into `NTT_ZERO` yields `w`.
pub fn ntt_ext_law<R: PolyRing>(w: R::NttForm) -> bool {
    let mut rebuilt = R::NTT_ZERO;
    for j in 0..R::N {
        rebuilt = R::with_ntt_coeff(rebuilt, j, R::ntt_coeff(w, j));
    }
    rebuilt == w
}
