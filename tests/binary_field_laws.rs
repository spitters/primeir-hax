//! The laws of `BinaryField` at the two reference instances of `GF(2^128)`
//! (`primeir_hax::gf128`), and one standards vector for each hash step.
//!
//! * GHASH: test case 2 of the GCM specification (McGrew and Viega, "The
//!   Galois/Counter Mode of Operation", Appendix B): key and plaintext zero,
//!   `H = 66e94bd4ef8a2c3b884cfa59ca342b2e`, ciphertext
//!   `0388dace60b6a392f328c2b971b2fe78`, and
//!   `GHASH(H, {}, C) = f38cbb1ad69223dcc3457ae5b6b0f885`.
//! * POLYVAL: RFC 8452, Appendix A, `POLYVAL(H, X_1, X_2)` with
//!   `H = 25629347589242761d31f826ba4b757b`.

use primeir_hax::binary::{ghash2_demo, gf_mul_add_demo, polyval2_demo, BinaryField};
use primeir_hax::gf128::{Ghash128, Polyval128, GHASH_X_INV_128, POLYVAL_X_INV_128};
use primeir_hax::laws;

fn hex16(s: &str) -> [u8; 16] {
    let b = s.as_bytes();
    assert_eq!(b.len(), 32);
    let mut out = [0u8; 16];
    for (i, o) in out.iter_mut().enumerate() {
        let hi = (b[2 * i] as char).to_digit(16).expect("hex digit") as u8;
        let lo = (b[2 * i + 1] as char).to_digit(16).expect("hex digit") as u8;
        *o = (hi << 4) | lo;
    }
    out
}

fn block<B: BinaryField>(s: &str) -> B {
    B::gf_from_bytes(&hex16(s))
}

fn bytes<B: BinaryField>(a: B) -> [u8; 16] {
    let mut out = [0u8; 16];
    a.gf_write_bytes(&mut out);
    out
}

/// Every law of `crate::laws` for `BinaryField`, on pseudorandom elements.
fn check_laws<B: BinaryField + core::fmt::Debug>(label: &str) {
    assert!(laws::binary_modulus_law::<B>(), "{label}: x^BITS is not MODULUS_LOW_LE");
    let mut s: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    for _ in 0..16 {
        let a = B::from_poly_le(&[next(), next()]);
        let b = B::from_poly_le(&[next(), next()]);
        let c = B::from_poly_le(&[next(), next(), next()]);
        assert!(laws::gf_add_law(a, b), "{label}: gf_add");
        assert!(laws::gf_mul_law(a, b, c), "{label}: gf_mul");
        assert!(laws::ghash_step_law(a, b, c), "{label}: ghash_step");
        assert!(laws::polyval_step_law(a, b, c), "{label}: polyval_step");
        assert!(laws::gf_bytes_roundtrip_law(a), "{label}: block codec");
        assert_eq!(gf_mul_add_demo(a, b, c), a.gf_mul(b).gf_add(c), "{label}: gf_mul_add_demo");
    }
}

#[test]
fn ghash_field_laws() {
    check_laws::<Ghash128>("Ghash128");
    let x_inv = Ghash128(GHASH_X_INV_128);
    assert_eq!(x_inv.gf_mul(laws::x_pow_bits::<Ghash128>()), Ghash128::ONE);
}

#[test]
fn polyval_field_laws() {
    check_laws::<Polyval128>("Polyval128");
    let x_inv = Polyval128(POLYVAL_X_INV_128);
    assert_eq!(x_inv.gf_mul(laws::x_pow_bits::<Polyval128>()), Polyval128::ONE);
}

#[test]
fn ghash_gcm_test_case_2() {
    let h: Ghash128 = block("66e94bd4ef8a2c3b884cfa59ca342b2e");
    let c: Ghash128 = block("0388dace60b6a392f328c2b971b2fe78");
    // len(A) = 0 and len(C) = 128, as two 64-bit big-endian integers.
    let len: Ghash128 = block("00000000000000000000000000000080");
    let tag = ghash2_demo(h, c, len);
    assert_eq!(bytes(tag), hex16("f38cbb1ad69223dcc3457ae5b6b0f885"));
}

#[test]
fn polyval_rfc8452_appendix_a() {
    let h: Polyval128 = block("25629347589242761d31f826ba4b757b");
    let x1: Polyval128 = block("4f4f95668c83dfb6401762bb2d01a262");
    let x2: Polyval128 = block("d1a24ddd2721d006bbe45f20d3c9f362");
    let s = polyval2_demo(h, x1, x2);
    assert_eq!(bytes(s), hex16("f7a3b47b846119fae5b7866cf5e5b77e"));
}
