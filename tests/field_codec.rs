//! The modulus item and the width-generic byte codec of `Field`, at every
//! reference instance: `MODULUS_LE` is the modulus of the arithmetic, `BYTES`
//! is its byte length, and `write_bytes` writes the canonical representative,
//! which `from_bytes` reads back.

use primeir_hax::laws;
use primeir_hax::Field;

/// `ZERO`, `ONE`, `−1` and 32 elements decoded from pseudorandom 64-byte
/// strings.
fn samples<F: Field>() -> Vec<F> {
    let mut v = vec![F::ZERO, F::ONE, F::ZERO.sub(F::ONE)];
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..32 {
        let mut b = [0u8; 64];
        for x in b.iter_mut() {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            *x = s as u8;
        }
        v.push(F::from_bytes(&b));
    }
    v
}

fn check_codec<F: Field>(label: &str, bytes: usize) {
    assert_eq!(F::BYTES, bytes, "{label}: BYTES");
    assert!(laws::bytes_width_law::<F>(), "{label}: BYTES is not the byte length of MODULUS_LE");
    assert!(laws::modulus_law::<F>(), "{label}: ZERO − ONE does not encode p − 1");
    for a in samples::<F>() {
        assert!(laws::bytes_roundtrip_law(a), "{label}: from_bytes does not invert write_bytes");
        assert!(laws::bytes_canonical_law(a), "{label}: write_bytes is not below p");
    }
    // `write_bytes` leaves the bytes beyond `BYTES` unchanged.
    let mut buf = [0xAAu8; 80];
    F::ONE.write_bytes(&mut buf);
    assert_eq!(buf[0], 1, "{label}: ONE encodes as 1");
    assert!(buf[1..F::BYTES].iter().all(|&x| x == 0), "{label}: ONE encodes as 1");
    assert!(buf[F::BYTES..].iter().all(|&x| x == 0xAA), "{label}: write_bytes wrote past BYTES");
}

#[test]
fn codec_mldsa_q() {
    check_codec::<primeir_hax::mldsa_q::Fq>("mldsa_q", 3);
    assert_eq!(<primeir_hax::mldsa_q::Fq as Field>::MODULUS_LE, &[8380417u64][..]);
}

#[test]
fn codec_mlkem_q() {
    check_codec::<primeir_hax::mlkem_q::Fq>("mlkem_q", 2);
    assert_eq!(<primeir_hax::mlkem_q::Fq as Field>::MODULUS_LE, &[3329u64][..]);
}

#[test]
fn codec_ext_ref_fp() {
    check_codec::<primeir_hax::ext_ref::Fp>("ext_ref::Fp", 4);
}

#[test]
fn to_byte_array_pads_with_zeros() {
    use primeir_hax::mldsa_q::Fq;
    let a = Fq(8380416);
    let b: [u8; 8] = primeir_hax::to_byte_array(a);
    assert_eq!(b, [0x00, 0xE0, 0x7F, 0, 0, 0, 0, 0]);
}

#[cfg(feature = "bigint-instances")]
#[test]
fn codec_bigint_instances() {
    use primeir_hax::fp25519::Fp25519;
    use primeir_hax::fp256::Fp256;
    check_codec::<Fp25519>("fp25519", 32);
    check_codec::<Fp256>("fp256", 32);
    assert_eq!(Fp25519::MODULUS_LE, &primeir_hax::FIELD_MODULUS_25519[..]);
    assert_eq!(Fp256::MODULUS_LE, &primeir_hax::FIELD_MODULUS_P256[..]);
}

#[cfg(feature = "fixed-width-instances")]
#[test]
fn codec_fp256_mont() {
    use primeir_hax::fp256_mont::Fp256Mont;
    check_codec::<Fp256Mont>("fp256_mont", 32);
    assert_eq!(Fp256Mont::MODULUS_LE, &primeir_hax::FIELD_MODULUS_P256[..]);
}
