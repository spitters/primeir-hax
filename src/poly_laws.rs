//! The law suite of [`PolyRing`], as generic checks.
//!
//! Every law stated in the contract of [`PolyRing`] is checked here on
//! pseudorandom inputs, for an arbitrary implementor. Each law is stated once,
//! as a Boolean function in [`crate::laws`] that the extraction also carries;
//! the checks here draw the inputs, supply the quantifier over indices and
//! assert the law. The entry point is [`check_poly_ring`]. A lattice
//! specification crate that implements the trait for its own types runs the
//! same suite against its instance:
//!
//! ```ignore
//! primeir_hax::poly_laws::check_poly_ring::<MyPoly>("my_poly", 0xA5A5, 3);
//! ```
//!
//! What the suite does **not** check is the evaluation ordering of `ntt` and
//! the shape of `basemul`: those are per-instance and are checked against the
//! scheme's specification, in `tests/lattice_kat.rs` (ML-DSA) and
//! `tests/mlkem_lattice_kat.rs` (ML-KEM).
//!
//! The module is `core`-only and gated out of the hax extraction: it is test
//! support that runs under rustc, not part of the surface an extraction sees.

use crate::laws;
use crate::poly::{
    mlwe_entry_demo, ntt_dot2_demo, ntt_residual_demo, ntt_sample_demo, poly_mul_demo, PolyRing,
};
use crate::Field;

/// The negacyclic product computed from the definition; stated with the laws
/// in [`crate::laws`] and re-exported here for the suites that compare an
/// instance against it.
pub use crate::laws::schoolbook_negacyclic;

/// The linear congruential generator of the pseudorandom inputs (the constants
/// of Knuth's MMIX), driving [`Field::from_bytes`] to produce coefficients.
pub struct Lcg {
    state: u64,
}

impl Lcg {
    /// A generator started at `seed`.
    pub const fn new(seed: u64) -> Self {
        Lcg { state: seed }
    }

    /// The next state.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state >> 33
    }

    /// A pseudorandom coefficient, by reducing eight little-endian bytes.
    pub fn coeff<F: Field>(&mut self) -> F {
        F::from_bytes(&self.next_u64().to_le_bytes())
    }

    /// A pseudorandom index below `n`.
    pub fn index(&mut self, n: usize) -> usize {
        (self.next_u64() as usize) % n
    }

    /// A pseudorandom element in coefficient form.
    pub fn poly<R: PolyRing>(&mut self) -> R {
        let mut p = R::ZERO;
        for i in 0..R::N {
            p = p.with_coeff(i, self.coeff::<R::Coeff>());
        }
        p
    }

    /// A pseudorandom element in NTT form, built entry by entry as a sampler in
    /// NTT form builds one.
    pub fn ntt_form<R: PolyRing>(&mut self) -> R::NttForm {
        let mut w = R::NTT_ZERO;
        for i in 0..R::N {
            w = R::with_ntt_coeff(w, i, self.coeff::<R::Coeff>());
        }
        w
    }
}

/// Law 6: `ZERO`, `coeff` and `with_coeff` present the coefficient vector.
pub fn check_coefficient_access<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    for i in 0..R::N {
        assert!(
            laws::zero_coeff_law::<R>(i),
            "{label}: ZERO has a nonzero coefficient at {i}"
        );
    }
    let c = rng.coeff::<R::Coeff>();
    let i = rng.index(R::N);
    assert!(
        laws::with_coeff_same_law(a, i, c),
        "{label}: with_coeff did not set coefficient {i}"
    );
    for j in 0..R::N {
        assert!(
            laws::with_coeff_other_law(a, i, c, j),
            "{label}: with_coeff at {i} changed coefficient {j}"
        );
    }
    assert!(
        laws::coeff_ext_law(a),
        "{label}: an element is not determined by its coefficients"
    );
    assert!(
        laws::poly_add_zero_law(a),
        "{label}: ZERO is not the unit of poly_add"
    );
}

/// Law 1, on the image of `ntt`: `intt ∘ ntt = id`, and `ntt ∘ intt = id` on an
/// element of `polyN` obtained as a transform. The second half of law 1 on an
/// arbitrary element of `polyN` is [`check_transform_bijection`].
pub fn check_transform_roundtrip<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    assert!(laws::intt_ntt_law(a), "{label}: intt ∘ ntt is not the identity");
    assert!(
        laws::ntt_intt_law::<R>(a.ntt()),
        "{label}: ntt ∘ intt is not the identity on the image of ntt"
    );
    assert!(laws::intt_ntt_law(R::ZERO), "{label}: the transform moves ZERO");
}

/// Law 1 on an arbitrary element of `polyN`, plus law 8 — the construction of
/// an element of `polyN` entry by entry.
pub fn check_transform_bijection<R: PolyRing>(rng: &mut Lcg, label: &str) {
    assert!(
        laws::ntt_zero_law::<R>(),
        "{label}: NTT_ZERO is not the transform of ZERO"
    );
    for i in 0..R::N {
        assert!(
            laws::ntt_zero_coeff_law::<R>(i),
            "{label}: NTT_ZERO has a nonzero entry at {i}"
        );
    }
    let w = rng.ntt_form::<R>();
    assert!(
        laws::ntt_intt_law::<R>(w),
        "{label}: ntt ∘ intt is not the identity on polyN"
    );
    let c = rng.coeff::<R::Coeff>();
    let i = rng.index(R::N);
    assert!(
        ntt_sample_demo::<R>(w, i, c) == R::with_ntt_coeff(w, i, c),
        "{label}: ntt_sample_demo is not with_ntt_coeff"
    );
    assert!(
        laws::with_ntt_coeff_same_law::<R>(w, i, c),
        "{label}: with_ntt_coeff did not set entry {i}"
    );
    for j in 0..R::N {
        assert!(
            laws::with_ntt_coeff_other_law::<R>(w, i, c, j),
            "{label}: with_ntt_coeff at {i} changed entry {j}"
        );
    }
    assert!(
        laws::ntt_ext_law::<R>(w),
        "{label}: an element of polyN is not determined by its N entries"
    );
}

/// Law 5: `poly_add`, `poly_sub` and `poly_smul` are coefficient-wise.
pub fn check_coefficient_wise_ops<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    let c = rng.coeff::<R::Coeff>();
    for i in 0..R::N {
        assert!(
            laws::poly_add_coeff_law(a, b, i),
            "{label}: poly_add is not coefficient-wise at {i}"
        );
        assert!(
            laws::poly_sub_coeff_law(a, b, i),
            "{label}: poly_sub is not coefficient-wise at {i}"
        );
        assert!(
            laws::poly_smul_coeff_law(a, c, i),
            "{label}: poly_smul is not coefficient-wise at {i}"
        );
    }
    assert!(
        laws::poly_sub_self_law(a),
        "{label}: poly_sub of an element with itself is not ZERO"
    );
    assert!(
        laws::poly_smul_one_law(a),
        "{label}: poly_smul by ONE is not the identity"
    );
}

/// Law 4, first half: `ntt_add` is the sum transported along the transform.
pub fn check_ntt_add<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        laws::ntt_add_law(a, b),
        "{label}: ntt_add is not the sum transported along the transform"
    );
    assert!(
        laws::intt_ntt_add_law(a, b),
        "{label}: intt of ntt_add is not the sum"
    );
    for i in 0..R::N {
        assert!(
            laws::ntt_add_entry_law::<R>(a.ntt(), b.ntt(), i),
            "{label}: ntt_add is not entry-wise at {i}"
        );
    }
}

/// Law 4, second half: `ntt_sub` is the difference transported along the
/// transform.
pub fn check_ntt_sub<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        laws::ntt_sub_law(a, b),
        "{label}: ntt_sub is not the difference transported along the transform"
    );
    assert!(
        laws::intt_ntt_sub_law(a, b),
        "{label}: intt of ntt_sub is not the difference"
    );
    for i in 0..R::N {
        assert!(
            laws::ntt_sub_entry_law::<R>(a.ntt(), b.ntt(), i),
            "{label}: ntt_sub is not entry-wise at {i}"
        );
    }
    assert!(
        laws::ntt_sub_self_law::<R>(a.ntt()),
        "{label}: ntt_sub of an element with itself is not the transform of ZERO"
    );
    assert!(
        laws::ntt_sub_add_law::<R>(a.ntt(), b.ntt()),
        "{label}: ntt_sub is not the inverse of ntt_add"
    );
}

/// Law 3: `basemul` is the ring product transported along the transform.
pub fn check_basemul<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        laws::basemul_law(a, b),
        "{label}: basemul is not the product transported along the transform"
    );
    assert!(
        laws::intt_basemul_law(a, b),
        "{label}: intt of basemul is not the ring product"
    );
    assert!(
        laws::basemul_comm_law::<R>(a.ntt(), b.ntt()),
        "{label}: basemul is not commutative"
    );
    assert!(
        laws::basemul_zero_law::<R>(a.ntt()),
        "{label}: basemul by the transform of ZERO is not the transform of ZERO"
    );
}

/// Law 2: `ntt_mul` is the negacyclic product of `Z_q[X]/(X^n + 1)`, checked
/// against the schoolbook convolution and against `X^(n−1)·X = −1`.
pub fn check_ntt_mul_is_negacyclic<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        laws::ntt_mul_negacyclic_law(a, b),
        "{label}: ntt_mul is not the schoolbook negacyclic product"
    );
    assert!(
        laws::ntt_mul_comm_law(a, b),
        "{label}: ntt_mul is not commutative"
    );
    assert!(
        laws::ntt_mul_one_law(a),
        "{label}: the constant 1 is not the unit of ntt_mul"
    );
    assert!(
        laws::ntt_mul_zero_law(a),
        "{label}: ZERO is not absorbing for ntt_mul"
    );
    assert!(
        laws::negacyclic_wrap_law::<R>(),
        "{label}: X^(n−1)·X is not −1, so the quotient is not by X^n + 1"
    );
}

/// Law 2, continued: `ntt_mul` is associative and distributes over `poly_add`.
pub fn check_ring_axioms<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    let c: R = rng.poly();
    assert!(
        laws::ntt_mul_assoc_law(a, b, c),
        "{label}: ntt_mul is not associative"
    );
    assert!(
        laws::ntt_mul_distrib_law(a, b, c),
        "{label}: ntt_mul does not distribute over poly_add"
    );
    let s = rng.coeff::<R::Coeff>();
    assert!(
        laws::ntt_mul_smul_law(a, b, s),
        "{label}: ntt_mul is not Coeff-bilinear"
    );
}

/// The generic callers of the surface compute what their names say.
pub fn check_generic_callers<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        poly_mul_demo(a, b) == schoolbook_negacyclic(a, b),
        "{label}: poly_mul_demo is not the ring product"
    );
    let s: R = rng.poly();
    let e: R = rng.poly();
    assert!(
        mlwe_entry_demo::<R>(a.ntt(), s, e) == schoolbook_negacyclic(a, s).poly_add(e),
        "{label}: mlwe_entry_demo is not a·s + e"
    );
    let v: R = rng.poly();
    let dot = ntt_dot2_demo::<R>(a.ntt(), b.ntt(), s.ntt(), v.ntt());
    assert!(
        R::intt(dot) == schoolbook_negacyclic(a, s).poly_add(schoolbook_negacyclic(b, v)),
        "{label}: ntt_dot2_demo is not a0·v0 + a1·v1"
    );
    let residual = ntt_residual_demo::<R>(a.ntt(), s.ntt(), b.ntt(), v.ntt());
    assert!(
        R::intt(residual) == schoolbook_negacyclic(a, s).poly_sub(schoolbook_negacyclic(b, v)),
        "{label}: ntt_residual_demo is not a·z − c·t"
    );
}

/// Every law of [`PolyRing`], on `rounds` pseudorandom inputs from `seed`.
pub fn check_poly_ring<R: PolyRing>(label: &str, seed: u64, rounds: usize) {
    assert!(R::N > 1, "{label}: the degree must exceed 1");
    let mut rng = Lcg::new(seed);
    for _ in 0..rounds {
        check_coefficient_access::<R>(&mut rng, label);
        check_transform_roundtrip::<R>(&mut rng, label);
        check_transform_bijection::<R>(&mut rng, label);
        check_coefficient_wise_ops::<R>(&mut rng, label);
        check_ntt_add::<R>(&mut rng, label);
        check_ntt_sub::<R>(&mut rng, label);
        check_basemul::<R>(&mut rng, label);
        check_ntt_mul_is_negacyclic::<R>(&mut rng, label);
        check_ring_axioms::<R>(&mut rng, label);
        check_generic_callers::<R>(&mut rng, label);
    }
}
