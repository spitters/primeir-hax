//! The binary-field op family of the prime-IR surface.
//!
//! [`BinaryField`] names the operations of a compiler's GF(2) polynomial
//! dialect (`gf2Dialect`, `Gf2Op`) on a binary field `GF(2^n) = GF(2)[x]/(f)`:
//! the sum, the product, and the two steps of the polynomial hashes of
//! AES-GCM (GHASH, NIST SP 800-38D) and AES-GCM-SIV (POLYVAL, RFC 8452). As
//! for the other families, each method carries the name of the operation it
//! denotes, and the realisation stays an opaque arithmetic leaf.
//!
//! | method          | `Gf2Op`      | meaning                                    |
//! |-----------------|--------------|--------------------------------------------|
//! | `gf_add`        | `xor`        | the sum (XOR)                              |
//! | `gf_mul`        | `mulReduced` | the product modulo `f`                     |
//! | `ghash_step`    | —            | `(acc + x)·h` (SP 800-38D, Algorithm 2)    |
//! | `polyval_step`  | —            | `(acc + x)·h·x^(−n)` (RFC 8452, Section 3) |
//! | `from_poly_le`  | —            | the element of a polynomial over GF(2)     |
//! | `gf_from_bytes`/`gf_write_bytes` | — | the block codec of the instance     |
//!
//! The byte order of a block is the instance's: GHASH reads bit `i` of a block
//! as the coefficient of `x^i` with the bits of each byte taken from the most
//! significant one (SP 800-38D, Section 6.3), POLYVAL reads a block as a
//! little-endian integer. [`BinaryField::from_poly_le`] is the
//! representation-independent constructor the laws use.
//!
//! The reference instances are `crate::gf128::Ghash128` (modulus
//! `x^128 + x^7 + x^2 + x + 1`) and `crate::gf128::Polyval128` (modulus
//! `x^128 + x^127 + x^126 + x^121 + 1`), gated out of the extraction.

/// A binary field `GF(2^n) = GF(2)[x]/(f)`, `f = x^n + r(x)` irreducible.
///
/// # The contract
///
/// Write `n` for [`BinaryField::BITS`]. An implementor must satisfy:
///
/// 1. `ZERO`, `ONE`, `gf_add` and `gf_mul` make `Self` the field
///    `GF(2)[x]/(f)`, where the low part `r` of `f` has the limbs
///    [`BinaryField::MODULUS_LOW_LE`]: `x^n == from_poly_le(MODULUS_LOW_LE)`.
/// 2. `from_poly_le(c)` is the residue of `Σ c_i·x^i`, where `c_i` is bit `i`
///    of the little-endian limbs `c`; `from_poly_le(&[1]) == ONE`.
/// 3. `ghash_step(acc, x, h) == acc.gf_add(x).gf_mul(h)`.
/// 4. `polyval_step(acc, x, h)·x^n == acc.gf_add(x).gf_mul(h)`.
/// 5. `gf_from_bytes` inverts `gf_write_bytes` on `BYTES = n / 8` bytes.
pub trait BinaryField: Copy + Clone + PartialEq {
    /// The degree `n` of the field over GF(2).
    const BITS: usize;
    /// The length in bytes of a block, `n / 8`.
    const BYTES: usize;
    /// The low part `r` of the modulus `f = x^n + r`, as little-endian `u64`
    /// limbs (bit `i` is the coefficient of `x^i`).
    const MODULUS_LOW_LE: &'static [u64];
    /// The zero polynomial.
    const ZERO: Self;
    /// The constant polynomial `1`.
    const ONE: Self;

    /// The residue of the polynomial whose coefficients are the bits of the
    /// little-endian limbs `coeffs`.
    fn from_poly_le(coeffs: &[u64]) -> Self;
    /// The sum. `Gf2Op.xor`.
    fn gf_add(self, rhs: Self) -> Self;
    /// The product modulo `f`. `Gf2Op.mulReduced`.
    fn gf_mul(self, rhs: Self) -> Self;
    /// One GHASH step, `(self + x)·h` (NIST SP 800-38D, Algorithm 2).
    fn ghash_step(self, x: Self, h: Self) -> Self;
    /// One POLYVAL step, `dot(self + x, h) = (self + x)·h·x^(−n)`
    /// (RFC 8452, Section 3).
    fn polyval_step(self, x: Self, h: Self) -> Self;
    /// The element of a block of `BYTES` bytes, in the instance's byte order.
    fn gf_from_bytes(bytes: &[u8]) -> Self;
    /// The block of `self` into `out[0..BYTES]`, in the instance's byte
    /// order. Requires `out.len() >= BYTES`.
    fn gf_write_bytes(self, out: &mut [u8]);
}

/// A generic caller of [`BinaryField::ghash_step`]: GHASH of two blocks,
/// `((x1·h) + x2)·h`. Not `cfg`-gated: the extraction must see it.
pub fn ghash2_demo<B: BinaryField>(h: B, x1: B, x2: B) -> B {
    B::ZERO.ghash_step(x1, h).ghash_step(x2, h)
}

/// A generic caller of [`BinaryField::polyval_step`]: POLYVAL of two blocks.
pub fn polyval2_demo<B: BinaryField>(h: B, x1: B, x2: B) -> B {
    B::ZERO.polyval_step(x1, h).polyval_step(x2, h)
}

/// A generic caller of [`BinaryField::gf_mul`] and [`BinaryField::gf_add`]:
/// `a·b + c`.
pub fn gf_mul_add_demo<B: BinaryField>(a: B, b: B, c: B) -> B {
    a.gf_mul(b).gf_add(c)
}
