//! Role-3 KATs for the `primeir-hax` reference instance.
//!
//! These drive the crate's *own* functions (rustc, not Lean) against published
//! constants and independent cross-checks — never a self-referential "KAT".
//!
//! * Field identities + a `num-bigint` cross-check of `mul`.
//! * The exact algebraic anchor `(p-1)^2 = 1 mod p`.
//! * The Montgomery contract.
//! * `pow` vs. repeated multiplication and vs. `inv`.
//! * The EC group law against RFC 8032 published values: `[L]B = O` and
//!   `[L+1]B = B`, where `L` is the published edwards25519 subgroup order and `B`
//!   the published base point.

use num_bigint::BigUint;
use primeir_hax::fp25519::{Edwards25519, Fp25519};
use primeir_hax::{EcGroup, Field, ModArith, Scalar};

/// `p = 2^255 - 19`, rebuilt independently in the test.
fn p() -> BigUint {
    (BigUint::from(1u8) << 255) - BigUint::from(19u8)
}

fn to_big(a: Fp25519) -> BigUint {
    BigUint::from_bytes_le(&a.to_bytes())
}

fn from_big(x: BigUint) -> Fp25519 {
    let le = (x % p()).to_bytes_le();
    Fp25519::from_bytes(&le)
}

/// A spread of field samples to test identities on.
fn samples() -> Vec<Fp25519> {
    vec![
        Fp25519::from_u64(2),
        Fp25519::from_u64(3),
        Fp25519::from_u64(0x1234_5678_9abc_def0),
        from_big(p() - BigUint::from(1u8)), // -1
        from_big((BigUint::from(1u8) << 200) + BigUint::from(7u8)),
    ]
}

#[test]
fn field_identities() {
    for &a in &samples() {
        // a * 1 = a
        assert_eq!(a.mul(Fp25519::ONE), a, "a*ONE=a");
        // a + 0 = a
        assert_eq!(a.add(Fp25519::ZERO), a, "a+ZERO=a");
        // a - a = 0
        assert_eq!(a.sub(a), Fp25519::ZERO, "a-a=ZERO");
        // a + (-a) = 0
        assert_eq!(a.add(a.neg()), Fp25519::ZERO, "a+(-a)=ZERO");
        // double = a + a
        assert_eq!(a.double(), a.add(a), "double=a+a");
        // square = a * a
        assert_eq!(a.square(), a.mul(a), "square=a*a");
        // a * inv(a) = 1  (a != 0)
        if a != Fp25519::ZERO {
            assert_eq!(a.mul(a.inv()), Fp25519::ONE, "a*inv(a)=ONE");
        }
        for &b in &samples() {
            for &c in &samples() {
                // distributivity: a*(b+c) = a*b + a*c
                assert_eq!(
                    a.mul(b.add(c)),
                    a.mul(b).add(a.mul(c)),
                    "distributivity"
                );
            }
            // cross-check mul against num-bigint directly
            let expect = from_big(to_big(a) * to_big(b));
            assert_eq!(a.mul(b), expect, "mul == num-bigint (a*b mod p)");
        }
    }
}

#[test]
fn minus_one_squared_is_one() {
    // (p-1) == -1 in the field, and (p-1)^2 = 1 mod p — an exact published anchor.
    let minus_one = from_big(p() - BigUint::from(1u8));
    assert_eq!(minus_one, Fp25519::ZERO.sub(Fp25519::ONE), "(p-1) = -1");
    assert_eq!(minus_one.square(), Fp25519::ONE, "(p-1)^2 = 1");
}

#[test]
fn montgomery_contract() {
    for &a in &samples() {
        // from_mont(to_mont(a)) = a
        assert_eq!(a.to_mont().from_mont(), a, "from_mont(to_mont a)=a");
        for &b in &samples() {
            // mont_mul(to_mont a, to_mont b) = to_mont(a*b)
            assert_eq!(
                a.to_mont().mont_mul(b.to_mont()),
                a.mul(b).to_mont(),
                "mont_mul(â,b̂)=â·b̂"
            );
        }
    }
}

#[test]
fn pow_matches_repeated_mul_and_inv() {
    let a = Fp25519::from_u64(5);
    // a^13 via pow vs. repeated multiply
    let mut expect = Fp25519::ONE;
    for _ in 0..13 {
        expect = expect.mul(a);
    }
    assert_eq!(a.pow(&[13]), expect, "a^13");

    // a^(p-2) = inv(a)
    let e = (p() - BigUint::from(2u8)).to_u64_digits();
    assert_eq!(a.pow(&e), a.inv(), "a^(p-2)=inv(a)");
}

/// The published edwards25519 subgroup order `L = 2^252 + 27742317...493`.
fn order_l() -> BigUint {
    (BigUint::from(1u8) << 252)
        + BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap()
}

fn scalar_of(x: &BigUint) -> Scalar {
    let mut bytes = [0u8; 32];
    let le = x.to_bytes_le();
    bytes[..le.len()].copy_from_slice(&le);
    Scalar::from_bytes_secret(bytes)
}

#[test]
fn base_point_is_on_curve() {
    // -x^2 + y^2 = 1 + d x^2 y^2  (edwards25519, a = -1).
    let b = Edwards25519::base_point();
    let (x, y) = b.to_affine();
    let lhs = x.square().neg().add(y.square());
    // d from the impl is private; recompute the RFC value here.
    let d = from_big(
        BigUint::parse_bytes(
            b"37095705934669439343138083508754565189542113879843219016388785533085940283555",
            10,
        )
        .unwrap(),
    );
    let rhs = Fp25519::ONE.add(d.mul(x.square()).mul(y.square()));
    assert_eq!(lhs, rhs, "base point satisfies the curve equation");
}

#[test]
fn ec_group_law_rfc8032_order() {
    let b = Edwards25519::base_point();
    let id = Edwards25519::IDENTITY;

    // identity laws
    assert_eq!(b.point_add(id), b, "B + O = B");
    assert_eq!(id.point_add(b), b, "O + B = B");
    // doubling agrees with scalar_mul(2)
    assert_eq!(
        b.point_double(),
        b.scalar_mul(scalar_of(&BigUint::from(2u8))),
        "2B via double = [2]B"
    );

    // The published-order anchors: [L]B = O and [L+1]B = B.
    let l = order_l();
    assert_eq!(b.scalar_mul(scalar_of(&l)), id, "[L]B = O");
    assert_eq!(
        b.scalar_mul(scalar_of(&(&l + BigUint::from(1u8)))),
        b,
        "[L+1]B = B"
    );
}
