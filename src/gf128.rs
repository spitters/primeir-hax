//! Reference instances of [`BinaryField`]: `GF(2^128)` at the GHASH modulus
//! (NIST SP 800-38D) and at the POLYVAL modulus (RFC 8452).
//!
//! Both store an element as a `u128` whose bit `i` is the coefficient of
//! `x^i`, and multiply by shift-and-add with reduction, most significant bit
//! of the multiplier first. They differ in the modulus and in the byte order
//! of a block:
//!
//! * [`Ghash128`]: `f = x^128 + x^7 + x^2 + x + 1`; bit `i` of a block is bit
//!   `7 − i mod 8` of byte `⌊i/8⌋` (SP 800-38D, Section 6.3).
//! * [`Polyval128`]: `f = x^128 + x^127 + x^126 + x^121 + 1`; a block is a
//!   little-endian integer (RFC 8452, Section 3).
//!
//! The constants `x^(−128)` of the two fields were computed with an
//! independent implementation and are checked by the tests
//! (`x^(−128)·x^128 = 1`). The module is the opaque arithmetic leaf: it is
//! gated out of the extraction, and it is not constant-time (it branches on
//! the bits of the multiplier).

use crate::binary::BinaryField;

/// The low part of the GHASH modulus, `x^7 + x^2 + x + 1`.
pub const GHASH_RED: u128 = 0x87;

/// The low part of the POLYVAL modulus, `x^127 + x^126 + x^121 + 1`.
pub const POLYVAL_RED: u128 = (1u128 << 127) | (1u128 << 126) | (1u128 << 121) | 1;

/// `x^(−128)` in the GHASH field.
pub const GHASH_X_INV_128: u128 = 0x5b02_1cae_93f7_8d45_b021_cae9_3f78_d477;

/// `x^(−128)` in the POLYVAL field.
pub const POLYVAL_X_INV_128: u128 = 0x9204_0000_0000_0000_0000_0000_0000_0001;

/// `a·x mod (x^128 + red)`.
fn mul_x(a: u128, red: u128) -> u128 {
    let top = a >> 127;
    let shifted = a << 1;
    if top == 1 {
        shifted ^ red
    } else {
        shifted
    }
}

/// `a·b mod (x^128 + red)`, by Horner's rule over the bits of `b`.
fn mul_mod(a: u128, b: u128, red: u128) -> u128 {
    let mut r = 0u128;
    let mut i = 128;
    while i > 0 {
        i -= 1;
        r = mul_x(r, red);
        if (b >> i) & 1 == 1 {
            r ^= a;
        }
    }
    r
}

/// The residue of `Σ c_i·x^i` modulo `x^128 + red`.
fn from_poly(coeffs: &[u64], red: u128) -> u128 {
    let mut r = 0u128;
    let mut j = coeffs.len();
    while j > 0 {
        j -= 1;
        let mut bit = 64;
        while bit > 0 {
            bit -= 1;
            r = mul_x(r, red) ^ (((coeffs[j] >> bit) & 1) as u128);
        }
    }
    r
}

/// The first 16 bytes of `bytes`, zero-padded.
fn block(bytes: &[u8]) -> [u8; 16] {
    let mut b = [0u8; 16];
    let n = if bytes.len() < 16 { bytes.len() } else { 16 };
    b[..n].copy_from_slice(&bytes[..n]);
    b
}

/// An element of `GF(2^128)` at the GHASH modulus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ghash128(pub u128);

/// An element of `GF(2^128)` at the POLYVAL modulus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Polyval128(pub u128);

impl BinaryField for Ghash128 {
    const BITS: usize = 128;
    const BYTES: usize = 16;
    const MODULUS_LOW_LE: &'static [u64] = &[0x87, 0];
    const ZERO: Self = Ghash128(0);
    const ONE: Self = Ghash128(1);

    fn from_poly_le(coeffs: &[u64]) -> Self {
        Ghash128(from_poly(coeffs, GHASH_RED))
    }
    fn gf_add(self, rhs: Self) -> Self {
        Ghash128(self.0 ^ rhs.0)
    }
    fn gf_mul(self, rhs: Self) -> Self {
        Ghash128(mul_mod(self.0, rhs.0, GHASH_RED))
    }
    fn ghash_step(self, x: Self, h: Self) -> Self {
        self.gf_add(x).gf_mul(h)
    }
    fn polyval_step(self, x: Self, h: Self) -> Self {
        self.gf_add(x).gf_mul(h).gf_mul(Ghash128(GHASH_X_INV_128))
    }
    /// Bit `i` of the element is bit `7 − i mod 8` of byte `⌊i/8⌋`: the
    /// big-endian integer of the block with its 128 bits reversed.
    fn gf_from_bytes(bytes: &[u8]) -> Self {
        Ghash128(u128::from_be_bytes(block(bytes)).reverse_bits())
    }
    fn gf_write_bytes(self, out: &mut [u8]) {
        out[..16].copy_from_slice(&self.0.reverse_bits().to_be_bytes());
    }
}

impl BinaryField for Polyval128 {
    const BITS: usize = 128;
    const BYTES: usize = 16;
    const MODULUS_LOW_LE: &'static [u64] = &[1, 0xC200_0000_0000_0000];
    const ZERO: Self = Polyval128(0);
    const ONE: Self = Polyval128(1);

    fn from_poly_le(coeffs: &[u64]) -> Self {
        Polyval128(from_poly(coeffs, POLYVAL_RED))
    }
    fn gf_add(self, rhs: Self) -> Self {
        Polyval128(self.0 ^ rhs.0)
    }
    fn gf_mul(self, rhs: Self) -> Self {
        Polyval128(mul_mod(self.0, rhs.0, POLYVAL_RED))
    }
    fn ghash_step(self, x: Self, h: Self) -> Self {
        self.gf_add(x).gf_mul(h)
    }
    fn polyval_step(self, x: Self, h: Self) -> Self {
        self.gf_add(x).gf_mul(h).gf_mul(Polyval128(POLYVAL_X_INV_128))
    }
    /// A block is the little-endian integer of its 16 bytes.
    fn gf_from_bytes(bytes: &[u8]) -> Self {
        Polyval128(u128::from_le_bytes(block(bytes)))
    }
    fn gf_write_bytes(self, out: &mut [u8]) {
        out[..16].copy_from_slice(&self.0.to_le_bytes());
    }
}
