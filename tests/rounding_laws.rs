//! The laws of `Rounding` at the two lattice moduli, with values computed by
//! hand from FIPS 203, Section 4.2.1 and FIPS 204, Algorithms 35 and 36.
//!
//! At `q = 3329` the compression laws are checked on every residue for the
//! widths `d ∈ {1, 4, 5, 10, 11}` that ML-KEM uses; at `q = 8380417` the laws
//! of `Power2Round` (`d = 13`), `Decompose` and the hints are checked for both
//! values of `γ2` of FIPS 204, Table 1, on the edges and on pseudorandom
//! residues.

use primeir_hax::laws;
use primeir_hax::rounding::{compress_roundtrip_demo, hint_demo, power2round_demo, Rounding};
use primeir_hax::Field;

#[test]
fn mlkem_compression() {
    use primeir_hax::mlkem_q::Fq;
    for d in [1u32, 4, 5, 10, 11] {
        for y in 0..(1u32 << d) {
            assert!(laws::compress_decompress_law::<Fq>(y, d), "d = {d}, y = {y}");
        }
        for x in 0..3329u32 {
            let a = Fq::new(x);
            assert!(laws::compress_range_law(a, d), "d = {d}, x = {x}");
            assert!(laws::decompress_compress_law(a, d), "d = {d}, x = {x}");
            assert_eq!(compress_roundtrip_demo(a, d), Fq::decompress_d(a.compress_d(d), d));
        }
    }
    // Compress_1 is the nearer of 0 and q/2: ⌈2·832/3329⌋ = 0,
    // ⌈2·833/3329⌋ = ⌈2·1665/3329⌋ = 1, ⌈2·3328/3329⌋ mod 2 = 0.
    assert_eq!(Fq::new(832).compress_d(1), 0);
    assert_eq!(Fq::new(833).compress_d(1), 1);
    assert_eq!(Fq::new(1665).compress_d(1), 1);
    assert_eq!(Fq::new(3328).compress_d(1), 0);
    assert_eq!(Fq::decompress_d(1, 1), Fq::new(1665));
}

/// The edges of `[0, q)` and of the rounding intervals, and pseudorandom
/// residues.
fn mldsa_samples(gamma2: u32) -> Vec<u64> {
    let q = 8380417u64;
    let g = gamma2 as u64;
    let mut v = vec![0, 1, q - 1, q - 2, g, g + 1, 2 * g, 2 * g + 1, q - 1 - g, 4095, 4096, 4097];
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..2000 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        v.push(s % q);
    }
    v
}

#[test]
fn mldsa_rounding() {
    use primeir_hax::mldsa_q::Fq;
    let q = 8380417u64;
    for gamma2 in [(q as u32 - 1) / 88, (q as u32 - 1) / 32] {
        let g = gamma2 as u64;
        let xs = mldsa_samples(gamma2);
        let zs: Vec<u64> = xs
            .iter()
            .take(40)
            .flat_map(|&s| [s % (g + 1), q - s % (g + 1)])
            .chain([0, 1, g, q - g, q - 1])
            .collect();
        for &x in &xs {
            let r = Fq::new(x);
            assert!(laws::power2round_law(r, 13), "power2round at {x}");
            assert!(laws::decompose_law(r, gamma2), "decompose at {x}, γ2 = {gamma2}");
            assert!(laws::high_low_bits_law(r, gamma2), "high/low bits at {x}");
            assert_eq!(power2round_demo(r, 13), r.power2round(13).0);
            for &z in zs.iter().take(12) {
                let z = Fq::new(z);
                assert!(laws::hint_law(z, r, gamma2), "hint at r = {x}, z = {z:?}, γ2 = {gamma2}");
                assert_eq!(hint_demo(z, r, gamma2), r.add(z).high_bits(gamma2));
            }
        }
        for &z in &zs {
            for &x in xs.iter().take(50) {
                assert!(laws::hint_law(Fq::new(z), Fq::new(x), gamma2), "hint at r = {x}, z = {z}");
            }
        }
        // r = q − 1 is the exceptional case of Decompose: (0, −1).
        assert_eq!(Fq::new(q - 1).decompose(gamma2), (0, -1));
    }
    // Power2Round(q − 1) = (1023, 0): q − 1 = 1023·2^13.
    assert_eq!(Fq::new(q - 1).power2round(13), (1023, 0));
    // Decompose(261889) with γ2 = (q − 1)/32 = 261888: 261889 mod± 523776 is
    // −261887, and the high part is 1.
    assert_eq!(Fq::new(261889).decompose(261888), (1, -261887));
}
