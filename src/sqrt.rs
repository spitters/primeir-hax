//! The square-root-of-a-ratio op of the prime-IR surface.
//!
//! [`SqrtRatio`] names the subroutine `sqrt_ratio(u, v)` of RFC 9380,
//! Appendix F.2.1, on top of the ring operations of [`Field`] and the
//! constant-time operations of [`CtField`]. It is the field operation that the
//! Simplified SWU map (RFC 9380, Appendix F.2) and the Elligator 2 map
//! (Section 6.7.1) use beyond those two families, and it is a fixed
//! straight-line program over the field (Appendices F.2.1.2 and F.2.1.3), so a
//! realisation is an arithmetic leaf like `inv` or `pow`.
//!
//! The subroutine is parameterised by the constant `Z` of the mapping
//! (Appendix F.2.1: "sqrt_ratio and map_to_curve_simple_swu MUST use the same
//! value for Z"). `Z` is the associated constant [`SqrtRatio::Z`] of the
//! realisation: a map written over `F: SqrtRatio` reads `F::Z` and calls
//! `F::sqrt_ratio`, so the two cannot disagree, and the constants that a
//! realisation precomputes from `Z` (`c2 = sqrt(-Z)` of Appendix F.2.1.2,
//! `c3 = sqrt(Z / c2)` of Appendix F.2.1.3) stay constants. A `Z` argument
//! would make them a computation at every call and would leave the agreement
//! between the map and its subroutine to the caller. A second suite with a
//! different `Z` over the same prime is a second field type over the same
//! representation.
//!
//! Truth values are `u64` values in `{0, 1}`, as in [`CtField`].

use crate::ct::CtField;
use crate::Field;

/// A prime field with the `sqrt_ratio` subroutine of RFC 9380, Appendix F.2.1,
/// for the mapping constant [`SqrtRatio::Z`].
pub trait SqrtRatio: CtField {
    /// Z, the constant of the mapping of the suite over this field (RFC 9380,
    /// Appendix F.2.1, parameter Z; Section 8 lists it per suite: 2 for
    /// curve25519 and edwards25519, -10 for P-256). Z is not a square in the
    /// field.
    const Z: Self;

    /// `sqrt_ratio(u, v)` (RFC 9380, Appendix F.2.1), for `v != 0`. Returns
    /// `(b, y)` with `b = 1` and `y = sqrt(u / v)` if `u / v` is a square in
    /// the field, and `b = 0` and `y = sqrt(Z * (u / v))` otherwise. The sign
    /// of `y` is not specified; the maps of RFC 9380, Section 6 fix the sign of
    /// their result themselves.
    fn sqrt_ratio(u: Self, v: Self) -> (u64, Self);
}

/// A generic caller of [`SqrtRatio::sqrt_ratio`], so that an extraction
/// contains a call site for it: the square root of `u / v` when it exists,
/// and zero otherwise. Not `cfg`-gated: the extraction must see it.
pub fn sqrt_ratio_demo<F: SqrtRatio>(u: F, v: F) -> F {
    let (is_square, y) = F::sqrt_ratio(u, v);
    F::ct_select(is_square, y, F::ZERO)
}

// --- Constants of the reference instances -----------------------------------

/// c1 = (q - 5) / 8 = 2^252 - 3 for q = 2^255 - 19 (RFC 9380, Appendix
/// F.2.1.3, constant 1), as four little-endian `u64` limbs, the form
/// `Field::pow` takes.
pub const SQRT_RATIO_5MOD8_C1_25519: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFD,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0x0FFF_FFFF_FFFF_FFFF,
];

/// c2 = sqrt(-1) for q = 2^255 - 19 (RFC 9380, Appendix F.2.1.3, constant 2):
/// 2^((q - 1) / 4), the SQRT_M1 of RFC 9496, Section 4.1, as little-endian
/// bytes.
///
/// c2 = 0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0
pub const SQRT_RATIO_5MOD8_C2_25519: [u8; 32] = [
    0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4,
    0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18, 0x43, 0x2f,
    0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b,
    0x0b, 0xdf, 0xc1, 0x4f, 0x80, 0x24, 0x83, 0x2b,
];

/// c3 = sqrt(Z / c2) for q = 2^255 - 19 and Z = 2 (RFC 9380, Appendix F.2.1.3,
/// constant 3): the root 1 - c2 = 1 - sqrt(-1), which is even, as
/// little-endian bytes. Its square is 2 / c2 = -2 * c2.
///
/// c3 = 0x547cdb7fb03e20f4d4b2ff66c2042858d0bce7f952d01b873b11e4d8b5f15f3e
pub const SQRT_RATIO_5MOD8_C3_25519: [u8; 32] = [
    0x3e, 0x5f, 0xf1, 0xb5, 0xd8, 0xe4, 0x11, 0x3b,
    0x87, 0x1b, 0xd0, 0x52, 0xf9, 0xe7, 0xbc, 0xd0,
    0x58, 0x28, 0x04, 0xc2, 0x66, 0xff, 0xb2, 0xd4,
    0xf4, 0x20, 0x3e, 0xb0, 0x7f, 0xdb, 0x7c, 0x54,
];

/// c1 = (q - 3) / 4 for the P-256 prime q = 2^256 - 2^224 + 2^192 + 2^96 - 1
/// (RFC 9380, Appendix F.2.1.2, constant 1), as four little-endian `u64`
/// limbs; 4 * c1 + 3 = q.
///
/// c1 = 0x3fffffffc00000004000000000000000000000003fffffffffffffffffffffff
pub const SQRT_RATIO_3MOD4_C1_P256: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_3FFF_FFFF,
    0x4000_0000_0000_0000,
    0x3FFF_FFFF_C000_0000,
];

/// c2 = sqrt(-Z) = sqrt(10) for the P-256 prime and Z = -10 (RFC 9380,
/// Appendix F.2.1.2, constant 2): the even root, as little-endian bytes.
///
/// c2 = 0x25ac71c31e27646736870398ae7f554d8472e008b3aa2a49d332cbd81bcc3b80
pub const SQRT_RATIO_3MOD4_C2_P256: [u8; 32] = [
    0x80, 0x3b, 0xcc, 0x1b, 0xd8, 0xcb, 0x32, 0xd3,
    0x49, 0x2a, 0xaa, 0xb3, 0x08, 0xe0, 0x72, 0x84,
    0x4d, 0x55, 0x7f, 0xae, 0x98, 0x03, 0x87, 0x36,
    0x67, 0x64, 0x27, 0x1e, 0xc3, 0x71, 0xac, 0x25,
];

// --- Reference instances ------------------------------------------------------
//
// Gated out of the extraction with the instances they extend. Each body is the
// straight-line program of the RFC over the trait operations of the instance.

/// `sqrt_ratio_5mod8` (RFC 9380, Appendix F.2.1.3) at q = 2^255 - 19 with
/// Z = 2, the Z of the curve25519 and edwards25519 suites (Section 8.5).
#[cfg(not(hax))]
impl SqrtRatio for crate::fp25519::Fp25519 {
    const Z: Self = crate::fp25519::Fp25519({
        let mut b = [0u8; 32];
        b[0] = 2;
        b
    });

    fn sqrt_ratio(u: Self, v: Self) -> (u64, Self) {
        let c2: Self = Self::from_bytes(&SQRT_RATIO_5MOD8_C2_25519);
        let c3: Self = Self::from_bytes(&SQRT_RATIO_5MOD8_C3_25519);
        // Step 1: tv1 = v^2.
        let tv1 = v.square();
        // Step 2: tv2 = tv1 * v.
        let tv2 = tv1.mul(v);
        // Step 3: tv1 = tv1^2.
        let tv1 = tv1.square();
        // Step 4: tv2 = tv2 * u.
        let tv2 = tv2.mul(u);
        // Step 5: tv1 = tv1 * tv2.
        let tv1 = tv1.mul(tv2);
        // Step 6: y1 = tv1^c1.
        let y1 = tv1.pow(&SQRT_RATIO_5MOD8_C1_25519);
        // Step 7: y1 = y1 * tv2.
        let y1 = y1.mul(tv2);
        // Step 8: tv1 = y1 * c2.
        let tv1 = y1.mul(c2);
        // Steps 9 and 10: tv2 = tv1^2 * v.
        let tv2 = tv1.square().mul(v);
        // Step 11: e1 = tv2 == u.
        let e1 = tv2.ct_eq(u);
        // Step 12: y1 = CMOV(y1, tv1, e1).
        let y1 = Self::ct_select(e1, tv1, y1);
        // Steps 13 and 14: tv2 = y1^2 * v.
        let tv2 = y1.square().mul(v);
        // Step 15: isQR = tv2 == u.
        let is_qr = tv2.ct_eq(u);
        // Step 16: y2 = y1 * c3.
        let y2 = y1.mul(c3);
        // Step 17: tv1 = y2 * c2.
        let tv1 = y2.mul(c2);
        // Steps 18 and 19: tv2 = tv1^2 * v.
        let tv2 = tv1.square().mul(v);
        // Step 20: tv3 = Z * u.
        let tv3 = Self::Z.mul(u);
        // Step 21: e2 = tv2 == tv3.
        let e2 = tv2.ct_eq(tv3);
        // Step 22: y2 = CMOV(y2, tv1, e2).
        let y2 = Self::ct_select(e2, tv1, y2);
        // Step 23: y = CMOV(y2, y1, isQR).
        let y = Self::ct_select(is_qr, y1, y2);
        // Step 24.
        (is_qr, y)
    }
}

/// `sqrt_ratio_3mod4` (RFC 9380, Appendix F.2.1.2) at the P-256 prime with
/// Z = -10, the Z of the P-256 suites (Section 8.2).
#[cfg(not(hax))]
impl SqrtRatio for crate::fp256::Fp256 {
    // Z = -10 = q - 10
    //   = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffff5,
    // as little-endian bytes.
    const Z: Self = crate::fp256::Fp256([
        0xf5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x01, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
    ]);

    fn sqrt_ratio(u: Self, v: Self) -> (u64, Self) {
        let c2: Self = Self::from_bytes(&SQRT_RATIO_3MOD4_C2_P256);
        // Step 1: tv1 = v^2.
        let tv1 = v.square();
        // Step 2: tv2 = u * v.
        let tv2 = u.mul(v);
        // Step 3: tv1 = tv1 * tv2.
        let tv1 = tv1.mul(tv2);
        // Step 4: y1 = tv1^c1.
        let y1 = tv1.pow(&SQRT_RATIO_3MOD4_C1_P256);
        // Step 5: y1 = y1 * tv2.
        let y1 = y1.mul(tv2);
        // Step 6: y2 = y1 * c2.
        let y2 = y1.mul(c2);
        // Steps 7 and 8: tv3 = y1^2 * v.
        let tv3 = y1.square().mul(v);
        // Step 9: isQR = tv3 == u.
        let is_qr = tv3.ct_eq(u);
        // Step 10: y = CMOV(y2, y1, isQR).
        let y = Self::ct_select(is_qr, y1, y2);
        // Step 11.
        (is_qr, y)
    }
}
