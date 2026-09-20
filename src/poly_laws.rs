//! The law suite of [`PolyRing`] and [`NttSample`], as generic checks.
//!
//! Every law stated in the contract of [`PolyRing`] and of [`NttSample`] is
//! checked here on pseudorandom inputs, for an arbitrary implementor. The two
//! entry points are [`check_poly_ring`] (the laws an implementor of
//! [`PolyRing`] must satisfy) and [`check_all`] (those plus the [`NttSample`]
//! laws). A lattice specification crate that implements the traits for its own
//! types runs the same suite against its instance:
//!
//! ```ignore
//! primeir_hax::poly_laws::check_all::<MyPoly>("my_poly", 0xA5A5, 3);
//! ```
//!
//! What the suite does **not** check is the evaluation ordering of `ntt` and
//! the shape of `basemul`: those are per-instance and are checked against the
//! scheme's specification, in `tests/lattice_kat.rs` (ML-DSA) and
//! `tests/mlkem_lattice_kat.rs` (ML-KEM).
//!
//! The module is `core`-only and gated out of the hax extraction: it is test
//! support that runs under rustc, not part of the surface an extraction sees.

use crate::poly::{mlwe_entry_demo, ntt_dot2_demo, ntt_sample_demo, poly_mul_demo, NttSample, PolyRing};
use crate::Field;

fn zero<F: Field>() -> F {
    F::ZERO
}

fn one<F: Field>() -> F {
    F::ONE
}

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
    pub fn ntt_form<R: NttSample>(&mut self) -> R::NttForm {
        let mut w = R::NTT_ZERO;
        for i in 0..R::N {
            w = R::with_ntt_coeff(w, i, self.coeff::<R::Coeff>());
        }
        w
    }
}

/// The negacyclic product of `Z_q[X]/(X^n + 1)` computed coefficient by
/// coefficient from the definition,
/// `(a·b)_k = Σ_{i+j=k} a_i·b_j − Σ_{i+j=k+n} a_i·b_j`.
/// The reference [`PolyRing::ntt_mul`] is checked against.
pub fn schoolbook_negacyclic<R: PolyRing>(a: R, b: R) -> R {
    let mut out = R::ZERO;
    for k in 0..R::N {
        let mut acc = zero::<R::Coeff>();
        for i in 0..=k {
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

/// Law 6: `ZERO`, `coeff` and `with_coeff` present the coefficient vector.
pub fn check_coefficient_access<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    for i in 0..R::N {
        assert!(
            R::ZERO.coeff(i) == zero::<R::Coeff>(),
            "{label}: ZERO has a nonzero coefficient at {i}"
        );
    }
    let c = rng.coeff::<R::Coeff>();
    let i = rng.index(R::N);
    let b = a.with_coeff(i, c);
    assert!(b.coeff(i) == c, "{label}: with_coeff did not set coefficient {i}");
    for j in 0..R::N {
        if j != i {
            assert!(
                b.coeff(j) == a.coeff(j),
                "{label}: with_coeff at {i} changed coefficient {j}"
            );
        }
    }
    let mut rebuilt = R::ZERO;
    for j in 0..R::N {
        rebuilt = rebuilt.with_coeff(j, a.coeff(j));
    }
    assert!(rebuilt == a, "{label}: an element is not determined by its coefficients");
    assert!(
        a.poly_add(R::ZERO) == a,
        "{label}: ZERO is not the unit of poly_add"
    );
}

/// Law 1, on the image of `ntt`: `intt ∘ ntt = id`, and `ntt ∘ intt = id` on an
/// element of `polyN` obtained as a transform. The second half of law 1 on an
/// arbitrary element of `polyN` needs [`NttSample`] and is
/// [`check_transform_bijection`].
pub fn check_transform_roundtrip<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    assert!(R::intt(a.ntt()) == a, "{label}: intt ∘ ntt is not the identity");
    assert!(
        R::intt(a.ntt()).ntt() == a.ntt(),
        "{label}: ntt ∘ intt is not the identity on the image of ntt"
    );
    assert!(R::intt(R::ZERO.ntt()) == R::ZERO, "{label}: the transform moves ZERO");
}

/// Law 1 on an arbitrary element of `polyN`, plus the [`NttSample`] contract.
pub fn check_transform_bijection<R: NttSample>(rng: &mut Lcg, label: &str) {
    assert!(
        R::NTT_ZERO == R::ZERO.ntt(),
        "{label}: NTT_ZERO is not the transform of ZERO"
    );
    for i in 0..R::N {
        assert!(
            R::ntt_coeff(R::NTT_ZERO, i) == zero::<R::Coeff>(),
            "{label}: NTT_ZERO has a nonzero entry at {i}"
        );
    }
    let w = rng.ntt_form::<R>();
    assert!(
        R::intt(w).ntt() == w,
        "{label}: ntt ∘ intt is not the identity on polyN"
    );
    let c = rng.coeff::<R::Coeff>();
    let i = rng.index(R::N);
    let v = ntt_sample_demo::<R>(w, i, c);
    assert!(
        R::ntt_coeff(v, i) == c,
        "{label}: with_ntt_coeff did not set entry {i}"
    );
    for j in 0..R::N {
        if j != i {
            assert!(
                R::ntt_coeff(v, j) == R::ntt_coeff(w, j),
                "{label}: with_ntt_coeff at {i} changed entry {j}"
            );
        }
    }
    let mut rebuilt = R::NTT_ZERO;
    for j in 0..R::N {
        rebuilt = R::with_ntt_coeff(rebuilt, j, R::ntt_coeff(w, j));
    }
    assert!(
        rebuilt == w,
        "{label}: an element of polyN is not determined by its N entries"
    );
}

/// Law 5: `poly_add`, `poly_sub` and `poly_smul` are coefficient-wise.
pub fn check_coefficient_wise_ops<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    let c = rng.coeff::<R::Coeff>();
    let sum = a.poly_add(b);
    let diff = a.poly_sub(b);
    let scaled = a.poly_smul(c);
    for i in 0..R::N {
        assert!(
            sum.coeff(i) == a.coeff(i).add(b.coeff(i)),
            "{label}: poly_add is not coefficient-wise at {i}"
        );
        assert!(
            diff.coeff(i) == a.coeff(i).sub(b.coeff(i)),
            "{label}: poly_sub is not coefficient-wise at {i}"
        );
        assert!(
            scaled.coeff(i) == c.mul(a.coeff(i)),
            "{label}: poly_smul is not coefficient-wise at {i}"
        );
    }
    assert!(
        a.poly_sub(a) == R::ZERO,
        "{label}: poly_sub of an element with itself is not ZERO"
    );
    assert!(
        a.poly_smul(one::<R::Coeff>()) == a,
        "{label}: poly_smul by ONE is not the identity"
    );
}

/// Law 4: `ntt_add` is the sum transported along the transform.
pub fn check_ntt_add<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        R::ntt_add(a.ntt(), b.ntt()) == a.poly_add(b).ntt(),
        "{label}: ntt_add is not the sum transported along the transform"
    );
    assert!(
        R::intt(R::ntt_add(a.ntt(), b.ntt())) == a.poly_add(b),
        "{label}: intt of ntt_add is not the sum"
    );
    for i in 0..R::N {
        assert!(
            R::ntt_coeff(R::ntt_add(a.ntt(), b.ntt()), i)
                == R::ntt_coeff(a.ntt(), i).add(R::ntt_coeff(b.ntt(), i)),
            "{label}: ntt_add is not entry-wise at {i}"
        );
    }
}

/// Law 3: `basemul` is the ring product transported along the transform.
pub fn check_basemul<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        R::basemul(a.ntt(), b.ntt()) == a.ntt_mul(b).ntt(),
        "{label}: basemul is not the product transported along the transform"
    );
    assert!(
        R::intt(R::basemul(a.ntt(), b.ntt())) == a.ntt_mul(b),
        "{label}: intt of basemul is not the ring product"
    );
    assert!(
        R::basemul(a.ntt(), b.ntt()) == R::basemul(b.ntt(), a.ntt()),
        "{label}: basemul is not commutative"
    );
    assert!(
        R::basemul(a.ntt(), R::ZERO.ntt()) == R::ZERO.ntt(),
        "{label}: basemul by the transform of ZERO is not the transform of ZERO"
    );
}

/// Law 2: `ntt_mul` is the negacyclic product of `Z_q[X]/(X^n + 1)`, checked
/// against the schoolbook convolution and against `X^(n−1)·X = −1`.
pub fn check_ntt_mul_is_negacyclic<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    assert!(
        a.ntt_mul(b) == schoolbook_negacyclic(a, b),
        "{label}: ntt_mul is not the schoolbook negacyclic product"
    );
    assert!(
        a.ntt_mul(b) == b.ntt_mul(a),
        "{label}: ntt_mul is not commutative"
    );
    let unit: R = constant::<R>(one::<R::Coeff>());
    assert!(a.ntt_mul(unit) == a, "{label}: the constant 1 is not the unit of ntt_mul");
    assert!(
        a.ntt_mul(R::ZERO) == R::ZERO,
        "{label}: ZERO is not absorbing for ntt_mul"
    );
    // X^(n−1) · X = X^n = −1.
    let x_top = R::ZERO.with_coeff(R::N - 1, one::<R::Coeff>());
    let x = R::ZERO.with_coeff(1, one::<R::Coeff>());
    let minus_one: R = constant::<R>(zero::<R::Coeff>().sub(one::<R::Coeff>()));
    assert!(
        x_top.ntt_mul(x) == minus_one,
        "{label}: X^(n−1)·X is not −1, so the quotient is not by X^n + 1"
    );
}

/// Law 2, continued: `ntt_mul` is associative and distributes over `poly_add`.
pub fn check_ring_axioms<R: PolyRing>(rng: &mut Lcg, label: &str) {
    let a: R = rng.poly();
    let b: R = rng.poly();
    let c: R = rng.poly();
    assert!(
        a.ntt_mul(b).ntt_mul(c) == a.ntt_mul(b.ntt_mul(c)),
        "{label}: ntt_mul is not associative"
    );
    assert!(
        a.ntt_mul(b.poly_add(c)) == a.ntt_mul(b).poly_add(a.ntt_mul(c)),
        "{label}: ntt_mul does not distribute over poly_add"
    );
    let s = rng.coeff::<R::Coeff>();
    assert!(
        a.ntt_mul(b.poly_smul(s)) == a.ntt_mul(b).poly_smul(s),
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
}

/// Every law of [`PolyRing`], on `rounds` pseudorandom inputs from `seed`.
pub fn check_poly_ring<R: PolyRing>(label: &str, seed: u64, rounds: usize) {
    assert!(R::N > 1, "{label}: the degree must exceed 1");
    let mut rng = Lcg::new(seed);
    for _ in 0..rounds {
        check_coefficient_access::<R>(&mut rng, label);
        check_transform_roundtrip::<R>(&mut rng, label);
        check_coefficient_wise_ops::<R>(&mut rng, label);
        check_ntt_add::<R>(&mut rng, label);
        check_basemul::<R>(&mut rng, label);
        check_ntt_mul_is_negacyclic::<R>(&mut rng, label);
        check_ring_axioms::<R>(&mut rng, label);
        check_generic_callers::<R>(&mut rng, label);
    }
}

/// Every law of [`PolyRing`] and of [`NttSample`].
pub fn check_all<R: NttSample>(label: &str, seed: u64, rounds: usize) {
    check_poly_ring::<R>(label, seed, rounds);
    let mut rng = Lcg::new(seed ^ 0x5DEE_CE66_D1B1_4A63);
    for _ in 0..rounds {
        check_transform_bijection::<R>(&mut rng, label);
    }
}
