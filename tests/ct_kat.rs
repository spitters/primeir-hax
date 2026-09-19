#![allow(clippy::needless_range_loop)]

//! `CtField` at the reference instance `Fp25519`.
//!
//! The negative field elements are the eight canonical encodings listed under
//! "Negative field elements" in RFC 9496, Appendix A.2. The full Appendix A
//! runs through this instance in `ristretto255-hax/tests/generic_vectors.rs`.

use primeir_hax::ct::{ct_abs_demo, ct_eq_up_to_sign_demo, CtField};
use primeir_hax::fp25519::Fp25519;
use primeir_hax::{Field, Scalar};

fn hex32(s: &str) -> [u8; 32] {
    let b = s.as_bytes();
    assert_eq!(b.len(), 64);
    let mut out = [0u8; 32];
    for i in 0..32 {
        let hi = (b[2 * i] as char).to_digit(16).expect("hex digit") as u8;
        let lo = (b[2 * i + 1] as char).to_digit(16).expect("hex digit") as u8;
        out[i] = (hi << 4) | lo;
    }
    out
}

/// RFC 9496, Appendix A.2, "Negative field elements".
const NEGATIVE_FIELD_ELEMENTS: [&str; 8] = [
    "0100000000000000000000000000000000000000000000000000000000000000",
    "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    "ed57ffd8c914fb201471d1c3d245ce3c746fcbe63a3679d51b6a516ebebe0e20",
    "c34c4e1826e5d403b78e246e88aa051c36ccf0aafebffe137d148a2bf9104562",
    "c940e5a4404157cfb1628b108db051a8d439e1a421394ec4ebccb9ec92a8ac78",
    "47cfc5497c53dc8e61c91d17fd626ffb1c49e2bca94eed052281b510b1117a24",
    "f1c6165d33367351b0da8f6e4511010c68174a03b6581212c71c0e1d026c3c72",
    "87260f7a2f12495118360f02c26a470f450dadf34a413d21042b43b9d93e1309",
];

#[test]
fn rfc9496_negative_field_elements() {
    for (i, s) in NEGATIVE_FIELD_ELEMENTS.iter().enumerate() {
        let bytes = hex32(s);
        let a = Fp25519::from_bytes(&bytes);
        assert_eq!(a.to_bytes(), bytes, "element {} is canonical", i);
        assert_eq!(a.is_negative(), 1, "element {} is negative", i);
        assert_eq!(a.neg().is_negative(), 0, "the negation of element {}", i);
        assert_eq!(a.ct_abs(), a.neg(), "absolute value of element {}", i);
        assert_eq!(a.neg().ct_abs(), a.neg(), "absolute value of the negation of {}", i);
        assert_eq!(ct_abs_demo(a), a.ct_abs(), "ct_abs_demo at element {}", i);
        assert_eq!(ct_eq_up_to_sign_demo(a, a.neg()), 1, "element {} and its negation", i);
    }
}

#[test]
fn zero_and_one() {
    let zero = Fp25519::ZERO;
    let one = Fp25519::ONE;
    assert_eq!(zero.is_zero(), 1);
    assert_eq!(one.is_zero(), 0);
    assert_eq!(zero.is_negative(), 0);
    assert_eq!(one.is_negative(), 1);
    // -1 = p - 1 = 2^255 - 20 is even.
    assert_eq!(one.neg().is_negative(), 0);
    assert_eq!(zero.ct_abs(), zero);
    assert_eq!(one.ct_abs(), one.neg());
    assert_eq!(ct_eq_up_to_sign_demo(zero, zero), 0);
}

#[test]
fn select_and_eq() {
    for n in 0..50u64 {
        let a = Fp25519::from_u64(n.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let b = Fp25519::from_u64(n.wrapping_mul(0xBF58_476D_1CE4_E5B9) ^ 1);
        assert_eq!(Fp25519::ct_select(1, a, b), a);
        assert_eq!(Fp25519::ct_select(0, a, b), b);
        assert_eq!(a.ct_eq(a), 1);
        assert_eq!(a.ct_eq(b) == 1, a == b);
        assert_eq!(a.sub(b).is_zero(), a.ct_eq(b));
        // Exactly one of a, -a is negative unless a = 0.
        assert_eq!(a.is_negative() + a.neg().is_negative() + a.is_zero(), 1);
    }
}

#[test]
fn scalar_bit_u64_agrees_with_bit() {
    let mut k = [0u8; 32];
    for i in 0..32 {
        k[i] = (i as u8).wrapping_mul(37) ^ 0xa5;
    }
    let s = Scalar::from_bytes_secret(k);
    for i in 0..256 {
        assert_eq!(s.bit_u64(i) == 1, s.bit(i), "bit {}", i);
        assert!(s.bit_u64(i) <= 1);
    }
}
