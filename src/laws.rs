//! The algebraic laws of the prime-IR traits, one Boolean function per law.
//!
//! Each function states one law of [`Field`], [`ModArith`], [`EcGroup`],
//! [`CtField`], [`SqrtRatio`], [`PolyRing`], [`ExtField`], [`BinaryField`] or
//! [`Rounding`] at the arguments it is given and returns whether the law holds
//! there. The same function serves two readers:
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

use crate::binary::BinaryField;
use crate::ct::CtField;
use crate::ext::ExtField;
use crate::poly::PolyRing;
use crate::rounding::Rounding;
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

// --- Field: the modulus and the byte codec ----------------------------------

/// The largest [`Field::BYTES`] the codec laws handle (1024-bit fields); above
/// it they hold vacuously.
pub const LAW_BYTES_MAX: usize = 128;

/// The number of bits of the integer with little-endian limbs `limbs`.
pub fn bit_length(limbs: &[u64]) -> usize {
    let mut bits = 0;
    for i in 0..limbs.len() {
        for b in 0..64 {
            if (limbs[i] >> b) & 1 == 1 {
                bits = 64 * i + b + 1;
            }
        }
    }
    bits
}

/// Limb `i` of the little-endian integer formed by the first `n` bytes of
/// `buf`.
fn limb_le(buf: &[u8], i: usize, n: usize) -> u64 {
    let mut v: u64 = 0;
    let mut j = 8;
    while j > 0 {
        j -= 1;
        let k = 8 * i + j;
        let byte = if k < n { buf[k] } else { 0 };
        v = (v << 8) | (byte as u64);
    }
    v
}

/// [`Field::BYTES`] is the byte length of the modulus,
/// `8·BYTES ≥ bitlen(p) > 8·(BYTES − 1)`, and the last limb of
/// [`Field::MODULUS_LE`] is nonzero.
pub fn bytes_width_law<F: Field>() -> bool {
    let p = F::MODULUS_LE;
    let bits = bit_length(p);
    p.len() > 0 && p[p.len() - 1] != 0 && 8 * F::BYTES >= bits && 8 * F::BYTES < bits + 8
}

/// [`Field::MODULUS_LE`] is the modulus of the arithmetic: the encoding of
/// `ZERO − ONE` is `p − 1`.
pub fn modulus_law<F: Field>() -> bool {
    let p = F::MODULUS_LE;
    if p.len() == 0 {
        false
    } else if F::BYTES > LAW_BYTES_MAX {
        true
    } else {
        let mut buf = [0u8; LAW_BYTES_MAX];
        F::ZERO.sub(F::ONE).write_bytes(&mut buf);
        let mut carry: u128 = 1;
        let mut ok = true;
        for i in 0..p.len() {
            let s = (limb_le(&buf, i, F::BYTES) as u128) + carry;
            ok = ok && (s as u64) == p[i];
            carry = s >> 64;
        }
        ok && carry == 0
    }
}

/// `from_bytes` inverts `write_bytes` ([`Field::write_bytes`]).
pub fn bytes_roundtrip_law<F: Field>(a: F) -> bool {
    if F::BYTES > LAW_BYTES_MAX {
        true
    } else {
        let mut buf = [0u8; LAW_BYTES_MAX];
        a.write_bytes(&mut buf);
        F::from_bytes(&buf) == a
    }
}

/// `write_bytes` writes the canonical representative: the integer it encodes
/// is below `p`.
pub fn bytes_canonical_law<F: Field>(a: F) -> bool {
    let p = F::MODULUS_LE;
    if F::BYTES > LAW_BYTES_MAX {
        true
    } else {
        let mut buf = [0u8; LAW_BYTES_MAX];
        a.write_bytes(&mut buf);
        let mut decided = false;
        let mut below = false;
        let mut i = p.len();
        while i > 0 {
            i -= 1;
            let x = limb_le(&buf, i, F::BYTES);
            if !decided && x != p[i] {
                decided = true;
                below = x < p[i];
            }
        }
        below
    }
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

/// Law 9: `basemul_acc` is the accumulated product,
/// `basemul_acc(acc, w, v) = ntt_add(acc, basemul(w, v))`.
pub fn basemul_acc_law<R: PolyRing>(acc: R::NttForm, w: R::NttForm, v: R::NttForm) -> bool {
    R::basemul_acc(acc, w, v) == R::ntt_add(acc, R::basemul(w, v))
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

// --- ExtField ---------------------------------------------------------------

/// `a^e` by square-and-multiply, `e` given as little-endian `u64` limbs.
pub fn ext_pow<E: ExtField>(a: E, exp: &[u64]) -> E {
    let mut acc = E::ONE;
    let mut j = exp.len();
    while j > 0 {
        j -= 1;
        let limb = exp[j];
        let mut bit = 64;
        while bit > 0 {
            bit -= 1;
            acc = acc.square();
            if (limb >> bit) & 1 == 1 {
                acc = acc.mul(a);
            }
        }
    }
    acc
}

/// `neg` is the additive inverse: `a + (−a) = 0`.
pub fn ext_add_neg_law<E: ExtField>(a: E) -> bool {
    a.add(a.neg()) == E::ZERO && a.sub(a) == E::ZERO && a.add(E::ZERO) == a
}

/// Commutativity of multiplication.
pub fn ext_mul_comm_law<E: ExtField>(a: E, b: E) -> bool {
    a.mul(b) == b.mul(a)
}

/// Associativity of multiplication.
pub fn ext_mul_assoc_law<E: ExtField>(a: E, b: E, c: E) -> bool {
    a.mul(b).mul(c) == a.mul(b.mul(c))
}

/// Distributivity of multiplication over addition.
pub fn ext_distrib_law<E: ExtField>(a: E, b: E, c: E) -> bool {
    a.mul(b.add(c)) == a.mul(b).add(a.mul(c))
}

/// `ONE` is the unit of multiplication.
pub fn ext_mul_one_law<E: ExtField>(a: E) -> bool {
    a.mul(E::ONE) == a
}

/// `square` is `a ↦ a·a`.
pub fn ext_square_law<E: ExtField>(a: E) -> bool {
    a.square() == a.mul(a)
}

/// `inv` is the inverse of a nonzero element; the law holds at `ZERO`.
pub fn ext_mul_inv_law<E: ExtField>(a: E) -> bool {
    if a == E::ZERO {
        true
    } else {
        a.mul(a.inv()) == E::ONE
    }
}

/// `mul_by_nonresidue` is the product with `NONRESIDUE`.
pub fn ext_mul_by_nonresidue_law<E: ExtField>(a: E) -> bool {
    a.mul_by_nonresidue() == a.mul(E::NONRESIDUE)
}

/// `conj` is `frobenius(DEGREE / 2)`, and an involution.
pub fn ext_conj_law<E: ExtField>(a: E) -> bool {
    a.conj() == a.frobenius(E::DEGREE / 2) && a.conj().conj() == a
}

/// `frobenius(·, 1)` is the `p`-th power, `p` the characteristic.
pub fn ext_frobenius_pow_law<E: ExtField>(a: E) -> bool {
    a.frobenius(1) == ext_pow(a, E::MODULUS_LE)
}

/// `frobenius(·, DEGREE)` is the identity.
pub fn ext_frobenius_period_law<E: ExtField>(a: E) -> bool {
    a.frobenius(E::DEGREE) == a
}

/// `frobenius(·, k)` is a ring homomorphism.
pub fn ext_frobenius_hom_law<E: ExtField>(a: E, b: E, k: usize) -> bool {
    a.mul(b).frobenius(k) == a.frobenius(k).mul(b.frobenius(k))
        && a.add(b).frobenius(k) == a.frobenius(k).add(b.frobenius(k))
}

/// `frobenius(frobenius(a, i), j) = frobenius(a, i + j)`.
pub fn ext_frobenius_compose_law<E: ExtField>(a: E, i: usize, j: usize) -> bool {
    a.frobenius(i).frobenius(j) == a.frobenius(i + j)
}

// --- BinaryField ------------------------------------------------------------

/// `x^BITS`, computed by repeated multiplication by `x`.
pub fn x_pow_bits<B: BinaryField>() -> B {
    let x = B::from_poly_le(&[2]);
    let mut acc = B::ONE;
    for _ in 0..B::BITS {
        acc = acc.gf_mul(x);
    }
    acc
}

/// The modulus is `x^BITS + r` with `r` given by `MODULUS_LOW_LE`, and
/// `from_poly_le(1) = ONE`.
pub fn binary_modulus_law<B: BinaryField>() -> bool {
    x_pow_bits::<B>() == B::from_poly_le(B::MODULUS_LOW_LE) && B::from_poly_le(&[1]) == B::ONE
}

/// `gf_add` is commutative, has `ZERO` as unit, and every element is its own
/// negative.
pub fn gf_add_law<B: BinaryField>(a: B, b: B) -> bool {
    a.gf_add(b) == b.gf_add(a) && a.gf_add(B::ZERO) == a && a.gf_add(a) == B::ZERO
}

/// `gf_mul` is commutative and associative, distributes over `gf_add`, and
/// has `ONE` as unit.
pub fn gf_mul_law<B: BinaryField>(a: B, b: B, c: B) -> bool {
    a.gf_mul(b) == b.gf_mul(a)
        && a.gf_mul(b).gf_mul(c) == a.gf_mul(b.gf_mul(c))
        && a.gf_mul(b.gf_add(c)) == a.gf_mul(b).gf_add(a.gf_mul(c))
        && a.gf_mul(B::ONE) == a
}

/// `ghash_step(acc, x, h) = (acc + x)·h`.
pub fn ghash_step_law<B: BinaryField>(acc: B, x: B, h: B) -> bool {
    acc.ghash_step(x, h) == acc.gf_add(x).gf_mul(h)
}

/// `polyval_step(acc, x, h)·x^BITS = (acc + x)·h`.
pub fn polyval_step_law<B: BinaryField>(acc: B, x: B, h: B) -> bool {
    acc.polyval_step(x, h).gf_mul(x_pow_bits::<B>()) == acc.gf_add(x).gf_mul(h)
}

/// `gf_from_bytes` inverts `gf_write_bytes` (blocks of at most 64 bytes;
/// vacuous above).
pub fn gf_bytes_roundtrip_law<B: BinaryField>(a: B) -> bool {
    if B::BYTES > 64 {
        true
    } else {
        let mut buf = [0u8; 64];
        a.gf_write_bytes(&mut buf);
        B::gf_from_bytes(&buf) == a
    }
}

// --- Rounding ---------------------------------------------------------------
//
// The laws read `q` as `MODULUS_LE[0]` and an element through its canonical
// encoding; a precondition that fails makes the law hold vacuously.

/// The canonical representative of `a`, for `BYTES ≤ 8` (zero otherwise).
pub fn canon_u64<F: Field>(a: F) -> u64 {
    let mut buf = [0u8; 8];
    if F::BYTES <= 8 {
        a.write_bytes(&mut buf);
    }
    limb_le(&buf, 0, 8)
}

/// The modulus `q` of a single-limb field.
fn modulus_q<F: Field>() -> u64 {
    F::MODULUS_LE[0]
}

/// `1 ≤ d` and `2^d < q`.
fn compress_width_ok<F: Field>(d: u32) -> bool {
    d >= 1 && d < 32 && (1u64 << d) < modulus_q::<F>()
}

/// `|x mod± q|` for `x ∈ [0, q)`.
fn centred_abs(x: u64, q: u64) -> u64 {
    if x > q - x {
        q - x
    } else {
        x
    }
}

/// `compress_d` lands in `[0, 2^d)`.
pub fn compress_range_law<F: Rounding>(a: F, d: u32) -> bool {
    if compress_width_ok::<F>(d) {
        (a.compress_d(d) as u64) < (1u64 << d)
    } else {
        true
    }
}

/// `compress_d(decompress_d(y, d), d) = y` for `y < 2^d` (FIPS 203, Section
/// 4.2.1).
pub fn compress_decompress_law<F: Rounding>(y: u32, d: u32) -> bool {
    if compress_width_ok::<F>(d) && (y as u64) < (1u64 << d) {
        F::decompress_d(y, d).compress_d(d) == y
    } else {
        true
    }
}

/// `|decompress_d(compress_d(r, d), d) − r mod± q| ≤ ⌈q / 2^(d+1)⌋` (FIPS
/// 203, Section 4.2.1).
pub fn decompress_compress_law<F: Rounding>(a: F, d: u32) -> bool {
    if compress_width_ok::<F>(d) {
        let q = modulus_q::<F>();
        let x = canon_u64(a);
        let y = canon_u64(F::decompress_d(a.compress_d(d), d));
        let dist = centred_abs((y + q - x) % q, q);
        dist <= (q + (1u64 << d)) >> (d + 1)
    } else {
        true
    }
}

/// `power2round(r, d) = (r1, r0)` with `r1·2^d + r0 ≡ r (mod q)` and
/// `−2^(d−1) < r0 ≤ 2^(d−1)` (FIPS 204, Algorithm 35).
pub fn power2round_law<F: Rounding>(a: F, d: u32) -> bool {
    if d >= 1 && d <= 30 {
        let q = modulus_q::<F>() as i64;
        let (r1, r0) = a.power2round(d);
        let half = 1i64 << (d - 1);
        let v = (r1 as i64) * (1i64 << d) + (r0 as i64);
        (r0 as i64) > -half && (r0 as i64) <= half && ((v % q) + q) % q == canon_u64(a) as i64
    } else {
        true
    }
}

/// `γ2 > 0` divides `(q − 1)/2`.
fn gamma2_ok<F: Field>(gamma2: u32) -> bool {
    let q = modulus_q::<F>();
    gamma2 > 0 && (q - 1) % (2 * gamma2 as u64) == 0
}

/// `decompose(r, γ2) = (r1, r0)` with `r1·2γ2 + r0 ≡ r (mod q)`,
/// `−γ2 ≤ r0 ≤ γ2` and `0 ≤ r1 < (q − 1)/2γ2` (FIPS 204, Algorithm 36).
pub fn decompose_law<F: Rounding>(a: F, gamma2: u32) -> bool {
    if gamma2_ok::<F>(gamma2) {
        let q = modulus_q::<F>() as i64;
        let g = gamma2 as i64;
        let (r1, r0) = a.decompose(gamma2);
        let v = (r1 as i64) * 2 * g + (r0 as i64);
        (r0 as i64) >= -g
            && (r0 as i64) <= g
            && (r1 as i64) < (q - 1) / (2 * g)
            && ((v % q) + q) % q == canon_u64(a) as i64
    } else {
        true
    }
}

/// `high_bits` and `low_bits` are the components of `decompose` (FIPS 204,
/// Algorithms 37 and 38).
pub fn high_low_bits_law<F: Rounding>(a: F, gamma2: u32) -> bool {
    if gamma2_ok::<F>(gamma2) {
        let (r1, r0) = a.decompose(gamma2);
        a.high_bits(gamma2) == r1 && a.low_bits(gamma2) == r0
    } else {
        true
    }
}

/// For `|z mod± q| ≤ γ2`, `use_hint(make_hint(z, r), r) = high_bits(r + z)`
/// (Lemma 1 of the CRYSTALS-Dilithium specification, `α = 2γ2`).
pub fn hint_law<F: Rounding>(z: F, r: F, gamma2: u32) -> bool {
    let q = modulus_q::<F>();
    if gamma2_ok::<F>(gamma2) && centred_abs(canon_u64(z), q) <= gamma2 as u64 {
        F::use_hint(F::make_hint(z, r, gamma2), r, gamma2) == r.add(z).high_bits(gamma2)
    } else {
        true
    }
}
