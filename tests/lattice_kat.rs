//! The `mldsa_q` reference instance of the prime-IR lattice surface against the
//! FIPS 204 specification crate `mldsa-hax` (validated with NIST ACVP vectors),
//! against the constants printed in FIPS 204, and against the definitions of
//! the operations (polynomial evaluation, the schoolbook negacyclic product).

use primeir_hax::mldsa_q::*;
use primeir_hax::poly::{
    mlwe_entry_demo, ntt_dot2_demo, ntt_residual_demo, ntt_sample_demo, poly_mul_demo, PolyRing,
    MODULUS_MLDSA,
};
use primeir_hax::poly_laws::check_poly_ring;
use primeir_hax::{Field, ModArith};

const Q: u32 = MODULUS_MLDSA;

fn lcg_poly(seed: u64) -> PolyDsa {
    let mut state = seed;
    let mut p = [0u32; 256];
    for c in p.iter_mut() {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *c = ((state >> 33) % Q as u64) as u32;
    }
    PolyDsa(p)
}

fn schoolbook_negacyclic(a: &PolyDsa, b: &PolyDsa) -> PolyDsa {
    let mut c = [Fq(0); 256];
    for i in 0..256 {
        for j in 0..256 {
            let t = Fq(a.0[i]).mul(Fq(b.0[j]));
            if i + j < 256 {
                c[i + j] = c[i + j].add(t);
            } else {
                c[i + j - 256] = c[i + j - 256].sub(t);
            }
        }
    }
    let mut out = [0u32; 256];
    for i in 0..256 {
        out[i] = c[i].0;
    }
    PolyDsa(out)
}

#[test]
fn modulus_and_constants_of_fips_204() {
    assert_eq!(Q, 8380417);
    assert_eq!(Q, mldsa_hax::Q);
    // Appendix B, first row; Algorithm 42's f.
    let row: Vec<u32> = (1..8).map(|k| zeta_pow(k).0).collect();
    assert_eq!(row, [4808194, 3765607, 3761513, 5178923, 5496691, 5234739, 5178987]);
    assert_eq!(Fq(256).inv(), Fq(INV_256));
    for k in 1..256 {
        assert_eq!(zeta_pow(k).0, mldsa_hax::ZETAS[k], "zetas[{k}]");
    }
}

#[test]
fn field_operations_agree_with_the_specification_crate() {
    let xs = [0u32, 1, 2, 1753, 4193792, Q / 2, Q - 2, Q - 1];
    for &a in &xs {
        for &b in &xs {
            assert_eq!(Fq(a).add(Fq(b)).0, mldsa_hax::add_mod_q(a, b));
            assert_eq!(Fq(a).sub(Fq(b)).0, mldsa_hax::sub_mod_q(a, b));
            assert_eq!(Fq(a).mul(Fq(b)).0, mldsa_hax::mul_mod_q(a, b));
        }
        assert_eq!(Fq(a).neg().0, mldsa_hax::sub_mod_q(0, a));
        assert_eq!(Fq(a).square(), Fq(a).mul(Fq(a)));
        assert_eq!(Fq(a).double(), Fq(a).add(Fq(a)));
        if a != 0 {
            assert_eq!(Fq(a).mul(Fq(a).inv()), Fq::ONE);
        }
        assert_eq!(Fq::from_bytes(&Fq(a).to_bytes()), Fq(a));
        assert_eq!(Fq(a).pow(&[3]), Fq(a).mul(Fq(a)).mul(Fq(a)));
    }
}

#[test]
fn montgomery_contract_with_radix_2_32() {
    assert_eq!(MONT_R, mldsa_hax::MONT_R);
    // R⁻¹ mod q.
    assert_eq!(Fq(MONT_R).inv(), Fq(8265825));
    for &a in &[0u32, 1, 12345, Q - 1] {
        for &b in &[1u32, 1753, Q - 2] {
            assert_eq!(Fq(a).to_mont().from_mont(), Fq(a));
            assert_eq!(Fq(a).to_mont().mont_mul(Fq(b).to_mont()), Fq(a).mul(Fq(b)).to_mont());
            // The signed Algorithm 49 of the specification crate computes the same residue.
            let prod = (a as i64) * (b as i64);
            let r = mldsa_hax::mont_reduce(prod) as i64;
            assert_eq!(r.rem_euclid(Q as i64) as u32, Fq(a).mont_mul(Fq(b)).0);
        }
    }
}

#[test]
fn transforms_agree_with_the_specification_crate() {
    for seed in 1..5u64 {
        let w = lcg_poly(seed);
        assert_eq!(w.ntt().0, mldsa_hax::ntt(&w.0), "ntt, seed {seed}");
        assert_eq!(PolyDsa::intt(NttDsa(w.0)).0, mldsa_hax::inv_ntt(&w.0), "intt, seed {seed}");
        assert_eq!(PolyDsa::intt(w.ntt()), w);
        let v = lcg_poly(seed + 50);
        assert_eq!(
            PolyDsa::basemul(NttDsa(w.0), NttDsa(v.0)).0,
            mldsa_hax::multiply_ntt(&w.0, &v.0)
        );
        assert_eq!(PolyDsa::ntt_add(w.ntt(), v.ntt()), w.poly_add(v).ntt());
        assert_eq!(PolyDsa::ntt_sub(w.ntt(), v.ntt()), w.poly_sub(v).ntt());
        assert_eq!(
            PolyDsa::ntt_sub(NttDsa(w.0), NttDsa(v.0)).0,
            mldsa_hax::poly_sub(&w.0, &v.0)
        );
        assert_eq!(w.poly_add(v).0, mldsa_hax::poly_add(&w.0, &v.0));
        assert_eq!(w.poly_sub(v).0, mldsa_hax::poly_sub(&w.0, &v.0));
        assert_eq!(w.poly_smul(Fq(1753)).0, mldsa_hax::poly_scalar_mul(1753, &w.0));
    }
}

#[test]
fn ntt_is_evaluation_at_bit_reversed_odd_powers() {
    // ŵ[i] = w(ζ^(2·BitRev8(i) + 1)): the order FIPS 204 fixes and ExpandA observes.
    let w = lcg_poly(7);
    let w_hat = w.ntt();
    for i in [0usize, 1, 2, 127, 128, 255] {
        let point = Fq(ZETA).pow(&[(2 * bit_rev_8(i) + 1) as u64]);
        let mut acc = Fq::ZERO;
        for j in (0..256).rev() {
            acc = acc.mul(point).add(w.coeff(j));
        }
        assert_eq!(PolyDsa::ntt_coeff(w_hat, i), acc, "index {i}");
    }
}

#[test]
fn ntt_mul_is_the_negacyclic_product() {
    for seed in 1..3u64 {
        let (a, b) = (lcg_poly(seed), lcg_poly(seed + 9));
        assert_eq!(poly_mul_demo(a, b), schoolbook_negacyclic(&a, &b));
    }
    // X^255 · X = −1.
    let x255 = PolyDsa::ZERO.with_coeff(255, Fq::ONE);
    let x = PolyDsa::ZERO.with_coeff(1, Fq::ONE);
    assert_eq!(x255.ntt_mul(x), PolyDsa::ZERO.with_coeff(0, Fq(Q - 1)));
}

#[test]
fn ntt_form_is_built_entry_by_entry() {
    // What ExpandA (FIPS 204 Algorithm 32) does: fill the entries of an element
    // of T_q directly, without applying the transform.
    let w = lcg_poly(11);
    let mut built = PolyDsa::NTT_ZERO;
    for i in 0..256 {
        built = ntt_sample_demo::<PolyDsa>(built, i, PolyDsa::ntt_coeff(w.ntt(), i));
    }
    assert_eq!(built, w.ntt());
    assert_eq!(PolyDsa::intt(built), w);
    assert_eq!(PolyDsa::NTT_ZERO, PolyDsa::ZERO.ntt());
}

#[test]
fn the_law_suite_of_the_surface() {
    check_poly_ring::<PolyDsa>("mldsa_q", 0x0204_0204, 3);
}

#[test]
fn mlwe_entry_is_a_times_s_plus_e() {
    let (a, s, e) = (lcg_poly(3), lcg_poly(4), lcg_poly(5));
    assert_eq!(mlwe_entry_demo::<PolyDsa>(a.ntt(), s, e), schoolbook_negacyclic(&a, &s).poly_add(e));
    // (a0·v0 + a1·v1) computed in NTT form.
    let (a1, v0, v1) = (lcg_poly(6), lcg_poly(8), lcg_poly(9));
    let dot = ntt_dot2_demo::<PolyDsa>(a.ntt(), a1.ntt(), v0.ntt(), v1.ntt());
    assert_eq!(
        PolyDsa::intt(dot),
        schoolbook_negacyclic(&a, &v0).poly_add(schoolbook_negacyclic(&a1, &v1))
    );
    // (a·z − c·t) computed in NTT form, the residual of Algorithm 8 line 11.
    let residual = ntt_residual_demo::<PolyDsa>(a.ntt(), v0.ntt(), a1.ntt(), v1.ntt());
    assert_eq!(
        PolyDsa::intt(residual),
        schoolbook_negacyclic(&a, &v0).poly_sub(schoolbook_negacyclic(&a1, &v1))
    );
}
