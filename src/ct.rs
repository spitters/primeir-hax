//! The constant-time op family of the prime-IR surface.
//!
//! [`CtField`] names the field operations that RFC 9496 (ristretto255, Sections
//! 2.1 and 2.2) and RFC 9380 (hash-to-curve, Section 4) use beyond the ring
//! operations of [`Field`]: selection, equality, the zero test, the sign and the
//! absolute value. A truth value is a `u64` in `{0, 1}`, so that a caller
//! combines conditions with `&` and `|` and passes them to
//! [`CtField::ct_select`] without a branch.
//!
//! | method        | RFC 9496        | meaning over `GF(p)`, `p` odd                         |
//! |---------------|-----------------|-------------------------------------------------------|
//! | `ct_select`   | §2.2 CT_SELECT  | `then_v` if `cond = 1`, `else_v` if `cond = 0`        |
//! | `ct_eq`       | §2.2 CT_EQ      | `1` if `a = b`, else `0`                              |
//! | `is_zero`     | —               | `1` if `a = 0`, else `0`                              |
//! | `is_negative` | §2.1 IS_NEGATIVE| parity of the representative of `a` in `[0, p)`       |
//! | `ct_abs`      | §2.2 CT_ABS     | `-a` if `is_negative(a) = 1`, else `a`                |
//!
//! The trait declares the identity of each operation. A realisation that
//! handles secret field elements must compute it in constant time; that
//! obligation lies on the realisation, and the reference instance below, which
//! is `num-bigint`-backed and compares and branches on values, does not meet
//! it.

use crate::{Field, Scalar};

/// A prime field of odd characteristic with the constant-time operations of
/// RFC 9496, Sections 2.1 and 2.2. Truth values are `u64` values in `{0, 1}`.
pub trait CtField: Field {
    /// CT_SELECT (RFC 9496, Section 2.2): `then_v` if `cond = 1` and `else_v`
    /// if `cond = 0`. The result is unspecified for any other `cond`.
    fn ct_select(cond: u64, then_v: Self, else_v: Self) -> Self;

    /// CT_EQ (RFC 9496, Section 2.2): `1` if `self` and `rhs` are the same
    /// field element, `0` otherwise.
    fn ct_eq(self, rhs: Self) -> u64;

    /// `1` if `self` is the zero of the field, `0` otherwise. Equal to
    /// `self.ct_eq(Self::ZERO)`.
    fn is_zero(self) -> u64;

    /// IS_NEGATIVE (RFC 9496, Section 2.1): the parity of the representative of
    /// `self` in `[0, p)`, that is `1` if that integer is odd and `0` if it is
    /// even. It is `sgn0` of RFC 9380, Section 4.1 for extension degree `m = 1`.
    fn is_negative(self) -> u64;

    /// CT_ABS (RFC 9496, Section 2.2): `-self` if `self.is_negative() = 1`,
    /// else `self`. The result is the one of `self`, `-self` that is not
    /// negative.
    fn ct_abs(self) -> Self;
}

impl Scalar {
    /// Little-endian bit `i` of the scalar, for `i < 256`, as a `u64` in
    /// `{0, 1}`. The value is secret; it is the condition of a
    /// [`CtField::ct_select`] in a double-and-add that does not branch on the
    /// scalar.
    pub fn bit_u64(&self, i: usize) -> u64 {
        let byte = self.0[i >> 3];
        ((byte >> (i & 7)) & 1) as u64
    }
}

/// A generic caller of [`CtField::ct_select`], [`CtField::is_negative`] and
/// [`Field::neg`], so that an extraction contains a call site for each: the
/// absolute value written out as a selection. Not `cfg`-gated: the extraction
/// must see it.
pub fn ct_abs_demo<F: CtField>(a: F) -> F {
    F::ct_select(a.is_negative(), a.neg(), a)
}

/// A generic caller of [`CtField::ct_eq`], [`CtField::is_zero`] and
/// [`CtField::ct_abs`]: `1` if `a` and `b` agree up to sign and are not zero.
pub fn ct_eq_up_to_sign_demo<F: CtField>(a: F, b: F) -> u64 {
    a.ct_abs().ct_eq(b.ct_abs()) & (1 - a.is_zero())
}

// The reference instance at `2^255 - 19`. It works on the canonical 32-byte
// representative that `Fp25519` stores, compares with `==` and selects with
// `if`, so it is not constant-time. Gated out of the extraction with the
// instance it extends.
#[cfg(not(hax))]
impl CtField for crate::fp25519::Fp25519 {
    fn ct_select(cond: u64, then_v: Self, else_v: Self) -> Self {
        if cond == 1 {
            then_v
        } else {
            else_v
        }
    }

    fn ct_eq(self, rhs: Self) -> u64 {
        if self.0 == rhs.0 {
            1
        } else {
            0
        }
    }

    fn is_zero(self) -> u64 {
        self.ct_eq(Self::ZERO)
    }

    fn is_negative(self) -> u64 {
        (self.0[0] & 1) as u64
    }

    fn ct_abs(self) -> Self {
        Self::ct_select(self.is_negative(), self.neg(), self)
    }
}
