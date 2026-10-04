//! The laws of `ExtField` at the reference tower `Fp2`, `Fp6`, `Fp12` over
//! `2^31 − 1` (`primeir_hax::ext_ref`), the embedding of each level into the
//! next, and the generic callers.

use primeir_hax::ext::{
    ext_conj_demo, ext_frobenius_demo, ext_mul_by_nonresidue_demo, ext_mul_demo, ExtField,
};
use primeir_hax::ext_ref::{Fp, Fp12, Fp2, Fp6, P, XI};
use primeir_hax::laws;
use primeir_hax::Field;

/// The xorshift generator of the inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn fp(&mut self) -> Fp {
        Fp::new(self.next())
    }
    fn fp2(&mut self) -> Fp2 {
        Fp2 {
            c0: self.fp(),
            c1: self.fp(),
        }
    }
    fn fp6(&mut self) -> Fp6 {
        Fp6 {
            c0: self.fp2(),
            c1: self.fp2(),
            c2: self.fp2(),
        }
    }
    fn fp12(&mut self) -> Fp12 {
        Fp12 {
            c0: self.fp6(),
            c1: self.fp6(),
        }
    }
}

/// Every law of `crate::laws` for `ExtField`, at `a`, `b`, `c`, and the
/// exact order of the Frobenius at `a`.
fn check_level<E: ExtField + core::fmt::Debug>(label: &str, a: E, b: E, c: E) {
    assert!(laws::ext_add_neg_law(a), "{label}: additive group");
    assert!(laws::ext_mul_comm_law(a, b), "{label}: mul is not commutative");
    assert!(laws::ext_mul_assoc_law(a, b, c), "{label}: mul is not associative");
    assert!(laws::ext_distrib_law(a, b, c), "{label}: mul does not distribute");
    assert!(laws::ext_mul_one_law(a), "{label}: ONE is not the unit");
    assert!(laws::ext_square_law(a), "{label}: square is not a·a");
    assert!(laws::ext_mul_inv_law(a), "{label}: inv is not the inverse");
    assert!(laws::ext_mul_inv_law(E::ZERO), "{label}: inv law at ZERO");
    assert!(laws::ext_mul_by_nonresidue_law(a), "{label}: mul_by_nonresidue");
    assert!(laws::ext_conj_law(a), "{label}: conj is not frobenius(DEGREE / 2)");
    assert!(laws::ext_frobenius_pow_law(a), "{label}: frobenius(1) is not the p-th power");
    assert!(laws::ext_frobenius_period_law(a), "{label}: frobenius(DEGREE) is not the identity");
    for k in [1, 2, 3, E::DEGREE - 1] {
        assert!(laws::ext_frobenius_hom_law(a, b, k), "{label}: frobenius({k}) is not a ring homomorphism");
    }
    assert!(laws::ext_frobenius_compose_law(a, 1, 2), "{label}: frobenius does not compose");
    assert!(
        laws::ext_frobenius_compose_law(a, E::DEGREE - 1, 3),
        "{label}: frobenius does not compose past DEGREE"
    );
    // A random element generates the field, so no proper power of the
    // Frobenius fixes it; this fails if the quotient splits.
    for k in 1..E::DEGREE {
        assert!(a.frobenius(k) != a, "{label}: frobenius({k}) fixes a random element");
    }
    // The generic callers.
    assert_eq!(ext_mul_demo(a, b), a.mul(b).add(a.mul(a)), "{label}: ext_mul_demo");
    assert_eq!(ext_conj_demo(a), a.mul(a.conj()), "{label}: ext_conj_demo");
    assert_eq!(ext_frobenius_demo(a, 1), laws::ext_pow(a, &[P]).mul(a), "{label}: ext_frobenius_demo");
}

#[test]
fn fp2_laws() {
    let mut r = Rng(0x0123_4567_89AB_CDEF);
    for _ in 0..8 {
        let (a, b, c) = (r.fp2(), r.fp2(), r.fp2());
        check_level("Fp2", a, b, c);
        // u^2 = −1.
        let u = Fp2::new(0, 1);
        assert_eq!(u.mul(u), Fp2::ONE.neg());
        // lift is an injective ring homomorphism from Fp.
        let (x, y) = (r.fp(), r.fp());
        assert_eq!(Fp2::lift(x.mul(y)), Fp2::lift(x).mul(Fp2::lift(y)));
        assert_eq!(Fp2::lift(x.add(y)), Fp2::lift(x).add(Fp2::lift(y)));
        assert_eq!(Fp2::lift(Fp::ONE), Fp2::ONE);
        // The Frobenius fixes the image of Fp.
        assert_eq!(Fp2::lift(x).frobenius(1), Fp2::lift(x));
    }
    assert_eq!(Fp2::NONRESIDUE, XI);
}

#[test]
fn fp6_laws() {
    let mut r = Rng(0xFEDC_BA98_7654_3210);
    for _ in 0..4 {
        let (a, b, c) = (r.fp6(), r.fp6(), r.fp6());
        check_level("Fp6", a, b, c);
        // v^3 = ξ.
        let v = Fp6::NONRESIDUE;
        assert_eq!(v.mul(v).mul(v), Fp6::lift(XI));
        let (x, y) = (r.fp2(), r.fp2());
        assert_eq!(Fp6::lift(x.mul(y)), Fp6::lift(x).mul(Fp6::lift(y)));
        assert_eq!(Fp6::lift(x.add(y)), Fp6::lift(x).add(Fp6::lift(y)));
        assert_eq!(Fp6::lift(Fp2::ONE), Fp6::ONE);
        // The Frobenius of Fp6 restricts to the one of Fp2.
        assert_eq!(Fp6::lift(x).frobenius(1), Fp6::lift(x.frobenius(1)));
        assert_eq!(ext_mul_by_nonresidue_demo(a, x), a.mul(v).add(Fp6::lift(x)));
    }
}

#[test]
fn fp12_laws() {
    let mut r = Rng(0x5555_AAAA_3333_CCCC);
    for _ in 0..2 {
        let (a, b, c) = (r.fp12(), r.fp12(), r.fp12());
        check_level("Fp12", a, b, c);
        // w^2 = v.
        let w = Fp12::NONRESIDUE;
        assert_eq!(w.mul(w), Fp12::lift(Fp6::NONRESIDUE));
        let (x, y) = (r.fp6(), r.fp6());
        assert_eq!(Fp12::lift(x.mul(y)), Fp12::lift(x).mul(Fp12::lift(y)));
        assert_eq!(Fp12::lift(x.add(y)), Fp12::lift(x).add(Fp12::lift(y)));
        assert_eq!(Fp12::lift(Fp6::ONE), Fp12::ONE);
        assert_eq!(Fp12::lift(x).frobenius(1), Fp12::lift(x.frobenius(1)));
        // conj is the p^6-power map, and a·conj(a) lies in Fp6.
        let n = ext_conj_demo(a);
        assert_eq!(n.c1, Fp6::ZERO);
    }
}
