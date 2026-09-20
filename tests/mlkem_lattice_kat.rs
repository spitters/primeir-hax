//! The `mlkem_q` reference instance of the prime-IR lattice surface against the
//! FIPS 203 specification crate `mlkem-hax` (validated with the NIST ML-KEM-768
//! KAT vectors), against the constants printed in FIPS 203, and against the
//! definitions of the operations.
//!
//! The instance is the generality check of the surface: ML-KEM's transform is
//! incomplete (7 layers, 128 quadratic factors), so an element in NTT form is a
//! vector of 128 pairs and `basemul` is 128 products of degree-1 polynomials.
//! The tests below pin that shape — the residue law of the transform, the
//! block-locality of `basemul`, and the failure of the entry-wise product —
//! alongside the generic law suite, which the instance passes unchanged.

use primeir_hax::mlkem_q::*;
use primeir_hax::poly::{PolyRing, MODULUS_MLKEM};
use primeir_hax::poly_laws::{check_poly_ring, schoolbook_negacyclic, Lcg};
use primeir_hax::Field;

const Q: u32 = MODULUS_MLKEM;

fn lcg_poly(seed: u64) -> PolyKem {
    Lcg::new(seed).poly::<PolyKem>()
}

#[test]
fn modulus_and_constants_of_fips_203() {
    assert_eq!(Q, 3329);
    assert_eq!(Q, mlkem_hax::Q);
    assert_eq!(ZETA, 17);
    assert_eq!(BLOCKS, 128);
    assert_eq!(PolyKem::N, mlkem_hax::N);
    // ζ is a primitive 256th root of unity: ζ^128 = −1, so ζ^256 = 1.
    assert_eq!(Fq(ZETA).pow(&[128]), Fq::ZERO.sub(Fq::ONE));
    assert_eq!(Fq(ZETA).pow(&[256]), Fq::ONE);
    // The transform has seven layers, so its inverse scales by 128⁻¹.
    assert_eq!(Fq(128).inv(), Fq(INV_128));
    assert_eq!(INV_128, 3303);
    // γ_i = ζ^(2·BitRev7(i)+1) and the 128 of them are the roots of the
    // quadratic factors: γ_i² runs over the primitive 256th roots.
    assert_eq!(gamma(0), Fq(ZETA));
    for i in 0..BLOCKS {
        assert_eq!(gamma(i), Fq(ZETA).pow(&[(2 * bit_rev_7(i) + 1) as u64]), "gamma {i}");
        assert_eq!(gamma(i).pow(&[128]), Fq::ZERO.sub(Fq::ONE), "gamma {i} order");
    }
}

#[test]
fn field_operations_agree_with_the_specification_crate() {
    let xs = [0u16, 1, 2, 17, 1665, 3327, 3328];
    for &a in &xs {
        for &b in &xs {
            assert_eq!(Fq(a).add(Fq(b)).0, mlkem_hax::field::add(a, b));
            assert_eq!(Fq(a).sub(Fq(b)).0, mlkem_hax::field::sub(a, b));
            assert_eq!(Fq(a).mul(Fq(b)).0, mlkem_hax::field::mul(a, b));
        }
        assert_eq!(Fq(a).neg().0, mlkem_hax::field::neg(a));
        assert_eq!(Fq(a).square(), Fq(a).mul(Fq(a)));
        assert_eq!(Fq(a).double(), Fq(a).add(Fq(a)));
        assert_eq!(Fq::from_bytes(&Fq(a).to_bytes()), Fq(a));
        assert_eq!(Fq(a).pow(&[3]), Fq(a).mul(Fq(a)).mul(Fq(a)));
        if a != 0 {
            assert_eq!(Fq(a).mul(Fq(a).inv()), Fq::ONE);
        }
    }
}

#[test]
fn transforms_agree_with_the_specification_crate() {
    for seed in 1..5u64 {
        let w = lcg_poly(seed);
        let v = lcg_poly(seed + 50);
        // Algorithm 9 and Algorithm 10.
        assert_eq!(flatten(w.ntt()), mlkem_hax::poly::ntt(&w.0), "ntt, seed {seed}");
        assert_eq!(
            PolyKem::intt(unflatten(w.0)).0,
            mlkem_hax::poly::inv_ntt(&w.0),
            "inv_ntt, seed {seed}"
        );
        // Algorithms 11 and 12: the crate's `ntt_mul` is the base-case multiply
        // of two elements already in NTT form, which is `basemul` here.
        assert_eq!(
            flatten(PolyKem::basemul(unflatten(w.0), unflatten(v.0))),
            mlkem_hax::poly::ntt_mul(&w.0, &v.0),
            "basemul, seed {seed}"
        );
        // The ring product, against the crate's schoolbook multiply.
        assert_eq!(w.ntt_mul(v).0, mlkem_hax::poly::poly_mul(&w.0, &v.0), "ntt_mul, seed {seed}");
        // The coefficient-wise operations.
        assert_eq!(w.poly_add(v).0, mlkem_hax::poly::poly_add(&w.0, &v.0));
        assert_eq!(w.poly_sub(v).0, mlkem_hax::poly::poly_sub(&w.0, &v.0));
        assert_eq!(w.poly_smul(Fq(17)).0, mlkem_hax::poly::poly_scalar(17, &w.0));
    }
}

#[test]
fn ntt_is_reduction_modulo_the_quadratic_factors() {
    // The incomplete transform: ŵ[2i] + ŵ[2i+1]·X = w mod (X² − γ_i), so
    // ŵ[2i] = Σ_m w[2m]·γ_i^m and ŵ[2i+1] = Σ_m w[2m+1]·γ_i^m. This is the
    // ordering ML-KEM's sampler of Â observes, and it is the statement that
    // replaces ML-DSA's "ŵ[i] is an evaluation at a single point".
    let w = lcg_poly(7);
    let w_hat = w.ntt();
    for i in [0usize, 1, 2, 63, 64, 127] {
        let g = gamma(i);
        let mut c0 = Fq::ZERO;
        let mut c1 = Fq::ZERO;
        for m in (0..BLOCKS).rev() {
            c0 = c0.mul(g).add(w.coeff(2 * m));
            c1 = c1.mul(g).add(w.coeff(2 * m + 1));
        }
        assert_eq!(PolyKem::ntt_coeff(w_hat, 2 * i), c0, "block {i}, constant term");
        assert_eq!(PolyKem::ntt_coeff(w_hat, 2 * i + 1), c1, "block {i}, linear term");
    }
}

#[test]
fn basemul_is_a_product_of_128_independent_quadratic_residues() {
    let a = lcg_poly(11).ntt();
    let b = lcg_poly(12).ntt();
    let c = PolyKem::basemul(a, b);
    // Each block is the product of two degree-1 polynomials modulo X² − γ_i.
    for i in 0..BLOCKS {
        let g = gamma(i);
        let (a0, a1) = (PolyKem::ntt_coeff(a, 2 * i), PolyKem::ntt_coeff(a, 2 * i + 1));
        let (b0, b1) = (PolyKem::ntt_coeff(b, 2 * i), PolyKem::ntt_coeff(b, 2 * i + 1));
        assert_eq!(
            PolyKem::ntt_coeff(c, 2 * i),
            a0.mul(b0).add(a1.mul(b1).mul(g)),
            "block {i}, constant term"
        );
        assert_eq!(
            PolyKem::ntt_coeff(c, 2 * i + 1),
            a0.mul(b1).add(a1.mul(b0)),
            "block {i}, linear term"
        );
    }
    // The blocks are independent: changing one entry of block 5 moves that
    // block of the product and nothing else.
    let mut a2 = a;
    a2.0[5][0] = Fq(a2.0[5][0]).add(Fq::ONE).0;
    let c2 = PolyKem::basemul(a2, b);
    for i in 0..BLOCKS {
        if i == 5 {
            assert_ne!(c2.0[i], c.0[i], "block 5 did not move");
        } else {
            assert_eq!(c2.0[i], c.0[i], "block {i} depends on block 5");
        }
    }
}

#[test]
fn basemul_is_not_the_entrywise_product() {
    // The transform is incomplete, so the multiplication of NTT form is not
    // entry-wise in Z_q: the linear terms of a block mix. (With a complete
    // transform, as ML-DSA's, it would be.)
    let a = lcg_poly(21).ntt();
    let b = lcg_poly(22).ntt();
    let c = PolyKem::basemul(a, b);
    let entrywise: Vec<u16> = (0..256)
        .map(|i| PolyKem::ntt_coeff(a, i).mul(PolyKem::ntt_coeff(b, i)).0)
        .collect();
    assert_ne!(flatten(c).to_vec(), entrywise);
}

#[test]
fn ntt_mul_is_the_negacyclic_product() {
    for seed in 1..3u64 {
        let (a, b) = (lcg_poly(seed), lcg_poly(seed + 9));
        assert_eq!(a.ntt_mul(b), schoolbook_negacyclic(a, b));
    }
    // X^255 · X = −1.
    let x255 = PolyKem::ZERO.with_coeff(255, Fq::ONE);
    let x = PolyKem::ZERO.with_coeff(1, Fq::ONE);
    assert_eq!(x255.ntt_mul(x), PolyKem::ZERO.with_coeff(0, Fq((Q - 1) as u16)));
}

#[test]
fn the_law_suite_of_the_surface() {
    check_poly_ring::<PolyKem>("mlkem_q", 0x0203_0203, 3);
}
