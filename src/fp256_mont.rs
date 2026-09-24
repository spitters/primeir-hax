//! Fixed-width instance of the prime field of NIST P-256, with no
//! allocation.
//!
//! `Fp256Mont` is the field of order `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`
//! (FIPS 186-4; RFC 9380, Section 8.2), stored as four little-endian `u64`
//! limbs in the Montgomery domain: the limbs of `x : Fp256Mont` hold the
//! integer `value(x) · R mod p` with `R = 2^256`. It carries the same trait
//! surface as [`crate::fp256::Fp256`], realised without `num-bigint` and
//! without a heap allocation on any path. The crate's own differential tests
//! check the limb arithmetic against the `num-bigint` reference instance,
//! including at the representative edges that drive the carry paths.
//!
//! ## Representation
//!
//! Every value this module hands back is **canonical**: the four limbs
//! denote an integer in `[0, p)`. Montgomery multiplication ends in a
//! conditional subtraction of `p`, and addition, subtraction and negation
//! each end in a conditional subtraction or addition of `p`, so no operation
//! returns a representative at or above `p`. Limb equality is therefore field
//! equality, which is why `PartialEq` is derived.
//!
//! ## The Montgomery parameters
//!
//! * `p` in little-endian limbs is [`P_LIMBS`], the same value as
//!   [`crate::FIELD_MODULUS_P256`].
//! * `p ≡ -1 (mod 2^64)`, so `-p^{-1} mod 2^64 = 1`: the per-word quotient of
//!   the reduction is the low word of the accumulator itself ([`N0INV`]).
//! * `R = 2^256 mod p = 2^224 - 2^192 - 2^96 + 1` is [`R_LIMBS`], which is
//!   also the Montgomery representation of `1` and hence [`Field::ONE`].
//! * `R^2 mod p` is [`R2_LIMBS`]; multiplying a canonical integer by it in the
//!   Montgomery domain is the map into the domain.
//!
//! ## Trait surface
//!
//! [`Field`], [`ModArith`], [`crate::ct::CtField`] and
//! [`crate::sqrt::SqrtRatio`] — the set [`crate::fp256::Fp256`] provides. No
//! [`crate::EcGroup`] instance: the P-256 group law is not part of this
//! module.
//!
//! `to_mont`, `from_mont` and `mont_mul` are the trait's operations *on field
//! values*, not on the internal representation: `to_mont` is `a ↦ a·R`, so on
//! Montgomery-stored limbs it is a Montgomery multiplication by `R^2`, and
//! `from_mont` is `a ↦ a·R^{-1}`, a Montgomery multiplication by `1`.
//!
//! ## Constant time
//!
//! `add`, `sub`, `neg`, `double`, `mul`, `square`, the conditional
//! subtraction inside every one of them, and the whole of [`CtField`] are
//! branch-free and index-free in the operand: selections are done with a
//! `0`/`all-ones` mask.
//!
//! [`Field::inv`] and [`SqrtRatio::sqrt_ratio`] reach their exponents through
//! `pow_c1_limbs`, whose addition chain is a straight line of squarings and
//! multiplications with no loop bound, branch or index that depends on the
//! operand. Both exponents are constants of the chain rather than data, so
//! there is no exponent to leak.
//!
//! [`Field::pow`] takes a runtime exponent and walks it in 4-bit windows. The
//! window digits index a 16-entry table of powers of the base and decide
//! whether a multiplication happens, so the memory trace and the operation
//! count are a function of the exponent. The index is a window digit of the
//! exponent, never of the base: `pow` is constant time in its base and not in
//! its exponent. Every exponent passed to `pow` in this crate is a public
//! constant, and the two exponents of the field's own callers (`p - 2` for
//! `inv`, `(p - 3)/4` for `sqrt_ratio`) do not reach it at all.
//!
//! ## Rust subset
//!
//! Index `while` loops, no iterator chains, no trait objects, no allocation,
//! `core` only: the subset hax extracts. Unlike the `num-bigint` reference
//! instances, the module is not gated out of the extraction; with the
//! `fixed-width-instances` feature it is on the extraction surface.

use crate::ct::CtField;
use crate::sqrt::{SqrtRatio, SQRT_RATIO_3MOD4_C2_P256};
use crate::{Field, ModArith};

// --- Montgomery parameters ---------------------------------------------------

/// `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`, as four little-endian `u64` limbs.
/// The same value as [`crate::FIELD_MODULUS_P256`].
pub const P_LIMBS: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

/// `-p^{-1} mod 2^64`. Because `p ≡ -1 (mod 2^64)`, this is `1`.
pub const N0INV: u64 = 1;

/// `q = 2^64 - 2^32 + 1`, the top limb of `p` and the only limb a reduction
/// round multiplies by (see [`mont_reduce`]).
const POLY3: u64 = 0xFFFF_FFFF_0000_0001;

/// `R = 2^256 mod p = 2^224 - 2^192 - 2^96 + 1`, as four little-endian `u64`
/// limbs. It is the Montgomery representation of the field element `1`.
pub const R_LIMBS: [u64; 4] = [
    0x0000_0000_0000_0001,
    0xFFFF_FFFF_0000_0000,
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFE,
];

/// `R^2 mod p`, as four little-endian `u64` limbs. It is the Montgomery
/// representation of the field element `R`, hence also of `2^256 mod p`.
pub const R2_LIMBS: [u64; 4] = [
    0x0000_0000_0000_0003,
    0xFFFF_FFFB_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFE,
    0x0000_0004_FFFF_FFFD,
];

/// `p - 2`, as four little-endian `u64` limbs: the Fermat exponent of
/// [`Field::inv`].
pub const P_MINUS_TWO: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFD,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

/// `(-10)·R mod p`: the Montgomery representation of `Z = -10`, the mapping
/// constant of the P-256 suites of RFC 9380, Section 8.2.
const Z_MONT_LIMBS: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFF5,
    0x0000_000A_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFF5_0000_000B,
];

/// The integer `1` in four little-endian `u64` limbs. Montgomery-multiplying
/// by it is the map out of the Montgomery domain.
const ONE_RAW: [u64; 4] = [1, 0, 0, 0];

// --- limb helpers -------------------------------------------------------------

/// `a + b` on 256-bit little-endian limbs: the low 256 bits and the carry out.
fn add_limbs(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], u64) {
    let mut r = [0u64; 4];
    let mut carry: u128 = 0;
    let mut i = 0;
    while i < 4 {
        let s = (a[i] as u128) + (b[i] as u128) + carry;
        r[i] = s as u64;
        carry = s >> 64;
        i += 1;
    }
    (r, carry as u64)
}

/// `a - b` on 256-bit little-endian limbs: the low 256 bits and the borrow
/// out, which is `1` exactly when `a < b`.
fn sub_limbs(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], u64) {
    let mut r = [0u64; 4];
    let mut borrow: u64 = 0;
    let mut i = 0;
    while i < 4 {
        // The u128 difference of two u64 values minus a bit is either below
        // 2^64 or wraps to a value whose bit 64 is set; that bit is the borrow.
        let d = (a[i] as u128)
            .wrapping_sub(b[i] as u128)
            .wrapping_sub(borrow as u128);
        r[i] = d as u64;
        borrow = ((d >> 64) & 1) as u64;
        i += 1;
    }
    (r, borrow)
}

/// `x` if `mask` is all ones and `y` if `mask` is zero, without a branch.
fn select_limbs(mask: u64, x: [u64; 4], y: [u64; 4]) -> [u64; 4] {
    let mut r = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        r[i] = (x[i] & mask) | (y[i] & !mask);
        i += 1;
    }
    r
}

/// The all-ones mask when `bit` is `1` and zero when `bit` is `0`.
fn mask_of(bit: u64) -> u64 {
    0u64.wrapping_sub(bit)
}

/// `lo + hi·2^256` reduced mod `p`, for an argument below `2p` (so `hi` is
/// `0` or `1`): one conditional subtraction, chosen without a branch.
fn reduce_once(lo: [u64; 4], hi: u64) -> [u64; 4] {
    let (d, borrow) = sub_limbs(lo, P_LIMBS);
    // The argument is at least p exactly when hi is set, or when the
    // subtraction of p from lo did not borrow.
    let take = hi | (borrow ^ 1);
    select_limbs(mask_of(take), d, lo)
}

/// `(a + b) mod p` for canonical `a`, `b`.
fn add_mod(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let (s, carry) = add_limbs(a, b);
    reduce_once(s, carry)
}

/// `(a - b) mod p` for canonical `a`, `b`: subtract, then add `p` back under
/// the borrow mask.
fn sub_mod(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let (d, borrow) = sub_limbs(a, b);
    let mask = mask_of(borrow);
    let mut addend = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        addend[i] = P_LIMBS[i] & mask;
        i += 1;
    }
    let (r, _) = add_limbs(d, addend);
    r
}

/// The shape of `p` that a Montgomery reduction round exploits.
///
/// Round `i` adds `m · p · 2^{64i}` with `m = t[i]`, which clears word `i`.
/// Writing `q = 2^64 - 2^32 + 1` ([`POLY3`]) for the top limb of `p`,
///
/// ```text
///   m·p·2^{64i} = -m·2^{64i}
///               + m·2^{64i+96} + m·2^{64i+192} - m·2^{64i+224} + m·2^{64i+256}
/// ```
///
/// The first term cancels `t[i]` exactly, with no borrow. The second is
/// `m·2^32` at words `i+1` and `i+2`, and the last three collect into
/// `m·2^{64(i+3)}·(2^64 - 2^32 + 1) = m·q·2^{64(i+3)}`, two words at `i+3`
/// and `i+4`. A round is therefore two shifts, one 64×64 product and four
/// word additions, against the four products of a general modulus.
///
/// The carry out of word `i+4` is the only value that leaves a round, and
/// word `i+5` is the highest word the next round touches, so it is held in
/// `pend` and folded into that round rather than propagated to the top of
/// the accumulator.
///
/// The argument must satisfy `t < p·2^256`, which holds for the product of
/// two canonical operands. The value handed to [`reduce_once`] is then
/// `(t + m·p)/2^256 < 2p`, so the final `pend` is `0` or `1`.
fn mont_reduce(mut t: [u64; 8]) -> [u64; 4] {
    let mut pend: u64 = 0;
    let mut i = 0;
    while i < 4 {
        let m = t[i].wrapping_mul(N0INV);
        let mp = (m as u128) * (POLY3 as u128);
        let s1 = (t[i + 1] as u128) + ((m << 32) as u128);
        t[i + 1] = s1 as u64;
        let s2 = (t[i + 2] as u128) + ((m >> 32) as u128) + (s1 >> 64);
        t[i + 2] = s2 as u64;
        let s3 = (t[i + 3] as u128) + ((mp as u64) as u128) + (s2 >> 64);
        t[i + 3] = s3 as u64;
        // Below 2^65, so the carry out is again a single bit.
        let s4 = (t[i + 4] as u128) + (mp >> 64) + (s3 >> 64) + (pend as u128);
        t[i + 4] = s4 as u64;
        pend = (s4 >> 64) as u64;
        i += 1;
    }
    reduce_once([t[4], t[5], t[6], t[7]], pend)
}

/// `a · b · R^{-1} mod p` for canonical `a`, `b`, by coarsely integrated
/// operand scanning: the running value is five words plus a carry word, and
/// each of the four passes adds one row `a · b[i]` of the product and then
/// reduces one word away.
///
/// The reduction round is the one of [`mont_reduce`] followed by the shift
/// down by a word, so the additions land at `acc[1..5]` and `acc[0]` leaves.
/// If `a` is canonical the running value stays below `2p`: a pass takes
/// `S` to `(S + a·b[i] + m·p)/2^64`, and `2p + p·(2^64-1) + (2^64-1)·p`
/// is `2p·2^64`. The accumulator therefore never needs a seventh word, and
/// `acc[4]` at the end is `0` or `1`.
fn mont_mul_limbs(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut acc = [0u64; 6];
    let mut i = 0;
    while i < 4 {
        // acc += a · b[i]. Each step is below 2^128:
        // (2^64-1) + (2^64-1)^2 + (2^64-1) = 2^128 - 1.
        let bi = b[i] as u128;
        let mut carry: u128 = 0;
        let mut j = 0;
        while j < 4 {
            let s = (acc[j] as u128) + (a[j] as u128) * bi + carry;
            acc[j] = s as u64;
            carry = s >> 64;
            j += 1;
        }
        let s = (acc[4] as u128) + carry;
        acc[4] = s as u64;
        acc[5] = (s >> 64) as u64;
        // One reduction round, then the shift down by a word.
        let m = acc[0].wrapping_mul(N0INV);
        let mp = (m as u128) * (POLY3 as u128);
        let s1 = (acc[1] as u128) + ((m << 32) as u128);
        let s2 = (acc[2] as u128) + ((m >> 32) as u128) + (s1 >> 64);
        let s3 = (acc[3] as u128) + ((mp as u64) as u128) + (s2 >> 64);
        let s4 = (acc[4] as u128) + (mp >> 64) + (s3 >> 64);
        let s5 = (acc[5] as u128) + (s4 >> 64);
        acc[0] = s1 as u64;
        acc[1] = s2 as u64;
        acc[2] = s3 as u64;
        acc[3] = s4 as u64;
        acc[4] = s5 as u64;
        acc[5] = 0;
        i += 1;
    }
    reduce_once([acc[0], acc[1], acc[2], acc[3]], acc[4])
}

/// `a · a · R^{-1} mod p` for canonical `a`, in ten 64×64 products rather
/// than the sixteen of a general product.
///
/// `a^2` is `2·C + D`, where `C` is the strictly upper triangle
/// `Σ_{i<j} a_i·a_j·2^{64(i+j)}` — six products, since `a_i·a_j = a_j·a_i` —
/// and `D` is the diagonal `Σ_i a_i^2·2^{128i}`, four products. `2·C ≤ a^2`
/// and `a^2 < 2^512`, so `C` is below `2^511` and the doubling stays inside
/// the eight words; the diagonal sum is `a^2` itself, so its carry out of
/// the top word is zero. `a^2 ≤ (p-1)^2 < p·2^256` is the precondition of
/// [`mont_reduce`].
fn mont_sqr_limbs(a: [u64; 4]) -> [u64; 4] {
    let mut t = [0u64; 8];
    // The strictly upper triangle. Row `i` ends at word `i+4`, which no
    // earlier row has written, so the row carry is a store rather than an add.
    let mut i = 0;
    while i < 4 {
        let mut carry: u128 = 0;
        let mut j = i + 1;
        while j < 4 {
            let s = (t[i + j] as u128) + (a[i] as u128) * (a[j] as u128) + carry;
            t[i + j] = s as u64;
            carry = s >> 64;
            j += 1;
        }
        t[i + 4] = carry as u64;
        i += 1;
    }
    // Double it.
    let mut bit: u64 = 0;
    let mut k = 0;
    while k < 8 {
        let top = t[k] >> 63;
        t[k] = (t[k] << 1) | bit;
        bit = top;
        k += 1;
    }
    // Add the diagonal, whose carry out of word `2i+1` lands on word `2i+2`.
    let mut c: u128 = 0;
    i = 0;
    while i < 4 {
        let sq = (a[i] as u128) * (a[i] as u128);
        let s = (t[2 * i] as u128) + ((sq as u64) as u128) + c;
        t[2 * i] = s as u64;
        let s2 = (t[2 * i + 1] as u128) + (sq >> 64) + (s >> 64);
        t[2 * i + 1] = s2 as u64;
        c = s2 >> 64;
        i += 1;
    }
    mont_reduce(t)
}

// --- exponentiation -------------------------------------------------------------

/// `a^(2^n)`: `n` Montgomery squarings.
fn sqr_n(a: [u64; 4], n: usize) -> [u64; 4] {
    let mut r = a;
    let mut i = 0;
    while i < n {
        r = mont_sqr_limbs(r);
        i += 1;
    }
    r
}

/// `a^c1` for `c1 = (p - 3)/4` ([`crate::sqrt::SQRT_RATIO_3MOD4_C1_P256`]), by
/// an addition chain of 253 squarings and 12 multiplications.
///
/// The chain follows the binary shape of `c1`, which is
///
/// ```text
///   [32 ones] [31 zeros] 1 [96 zeros] [94 ones]
/// ```
///
/// (254 bits). Writing `o(k)` for `a^(2^k - 1)`, five doubling steps
/// `o(2k) = o(k)^(2^k) · o(k)` carry `o(1) = a` up to `o(32)`, the top
/// segment. The accumulator then walks down the exponent, one shift-and-multiply
/// per segment: `<< 32` and `· a` closes `[32 ones][31 zeros]1`, `<< 128` and
/// `· o(32)` crosses the 96 zeros and lays the first 32 of the low ones, and
/// `32 + 16 + 8 + 4 + 2` more ones complete the run of 94.
///
/// Every step is unconditional, so the operation sequence is the same for
/// every `a`.
fn pow_c1_limbs(a: [u64; 4]) -> [u64; 4] {
    // Runs of ones: o(k) = a^(2^k - 1).
    let o1 = a;
    let o2 = mont_mul_limbs(sqr_n(o1, 1), o1);
    let o4 = mont_mul_limbs(sqr_n(o2, 2), o2);
    let o8 = mont_mul_limbs(sqr_n(o4, 4), o4);
    let o16 = mont_mul_limbs(sqr_n(o8, 8), o8);
    let o32 = mont_mul_limbs(sqr_n(o16, 16), o16);
    // [32 ones][31 zeros]1
    let acc = mont_mul_limbs(sqr_n(o32, 32), o1);
    // [96 zeros] and the first 32 of the low ones.
    let acc = mont_mul_limbs(sqr_n(acc, 128), o32);
    // The remaining 32 + 16 + 8 + 4 + 2 = 62 low ones.
    let acc = mont_mul_limbs(sqr_n(acc, 32), o32);
    let acc = mont_mul_limbs(sqr_n(acc, 16), o16);
    let acc = mont_mul_limbs(sqr_n(acc, 8), o8);
    let acc = mont_mul_limbs(sqr_n(acc, 4), o4);
    mont_mul_limbs(sqr_n(acc, 2), o2)
}

/// The little-endian byte encoding of four little-endian limbs.
fn limbs_to_bytes_le(v: [u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 4 {
        let mut j = 0;
        while j < 8 {
            out[8 * i + j] = (v[i] >> (8 * j)) as u8;
            j += 1;
        }
        i += 1;
    }
    out
}

/// The four little-endian limbs of a little-endian 32-byte encoding.
fn bytes_le_to_limbs(b: &[u8; 32]) -> [u64; 4] {
    let mut v = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        let mut acc: u64 = 0;
        let mut j = 8;
        while j > 0 {
            j -= 1;
            acc = (acc << 8) | (b[8 * i + j] as u64);
        }
        v[i] = acc;
        i += 1;
    }
    v
}

// --- Fp256Mont ------------------------------------------------------------------

/// An element of `GF(p)` for the P-256 prime, held as four little-endian
/// `u64` limbs of `value · R mod p` in `[0, p)`.
///
/// The representative is canonical (see the module documentation), so
/// `PartialEq` on the limbs is equality in the field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp256Mont(pub [u64; 4]);

impl Fp256Mont {
    /// The field element whose value is `2^256 mod p = R`. Its Montgomery
    /// representation is `R^2 mod p`. [`Field::from_bytes`] uses it as the
    /// weight of each 32-byte chunk beyond the lowest.
    pub const TWO_POW_256: Self = Fp256Mont(R2_LIMBS);

    /// The field element of the small integer `n`.
    pub fn from_u64(n: u64) -> Self {
        Fp256Mont(mont_mul_limbs([n, 0, 0, 0], R2_LIMBS))
    }

    /// The field element of a little-endian 32-byte integer, reduced mod `p`.
    /// Any 256-bit integer is below `2p`, so the reduction is one conditional
    /// subtraction.
    pub fn from_canonical_bytes(b: &[u8; 32]) -> Self {
        let v = reduce_once(bytes_le_to_limbs(b), 0);
        Fp256Mont(mont_mul_limbs(v, R2_LIMBS))
    }

    /// The four little-endian limbs of the canonical representative in
    /// `[0, p)`, that is of `value` rather than of `value · R`.
    pub fn to_canonical_limbs(self) -> [u64; 4] {
        mont_mul_limbs(self.0, ONE_RAW)
    }
}

impl Field for Fp256Mont {
    const ZERO: Self = Fp256Mont([0, 0, 0, 0]);
    /// `R`, the Montgomery representation of `1`.
    const ONE: Self = Fp256Mont(R_LIMBS);

    fn add(self, rhs: Self) -> Self {
        Fp256Mont(add_mod(self.0, rhs.0))
    }

    fn sub(self, rhs: Self) -> Self {
        Fp256Mont(sub_mod(self.0, rhs.0))
    }

    /// Montgomery multiplication of the two representatives: `(aR)(bR)/R =
    /// (ab)R`, the representative of the product.
    fn mul(self, rhs: Self) -> Self {
        Fp256Mont(mont_mul_limbs(self.0, rhs.0))
    }

    fn neg(self) -> Self {
        Fp256Mont(sub_mod([0, 0, 0, 0], self.0))
    }

    /// Montgomery squaring of the representative, through the ten-product
    /// [`mont_sqr_limbs`] rather than [`mont_mul_limbs`] at equal operands.
    fn square(self) -> Self {
        Fp256Mont(mont_sqr_limbs(self.0))
    }

    fn double(self) -> Self {
        Fp256Mont(add_mod(self.0, self.0))
    }

    /// `self^(p-2)` (Fermat), through the addition chain of `pow_c1_limbs`.
    /// Since `4·c1 + 3 = p`, the Fermat exponent is `p - 2 = 4·c1 + 1`, which
    /// is two further squarings and one multiplication past `c1`: 255
    /// squarings and 13 multiplications in all, against the 256 squarings and
    /// 128 multiplications of a bit-by-bit walk of [`P_MINUS_TWO`]. The value
    /// at `ZERO` is `ZERO`, which the trait leaves unspecified.
    fn inv(self) -> Self {
        let c1 = pow_c1_limbs(self.0);
        Fp256Mont(mont_mul_limbs(sqr_n(c1, 2), self.0))
    }

    /// `self^exp` for a runtime exponent, by a fixed 4-bit window: a table of
    /// `self^0 … self^15`, then four squarings and at most one multiplication
    /// per window, most significant limb and window first. A window is 4 bits
    /// and a limb is 64, so no window straddles a limb boundary, and windows
    /// above the leading non-zero one are skipped. A dense 256-bit exponent
    /// costs 14 + 252 + 63 operations against the 256 + 256 of a bit-by-bit
    /// walk.
    ///
    /// Which table entry is read and whether a multiplication happens are
    /// functions of the exponent, which is public at every call site (see the
    /// module documentation).
    fn pow(self, exp: &[u64]) -> Self {
        // table[d] = self^d.
        let mut table = [[0u64; 4]; 16];
        table[0] = Self::ONE.0;
        table[1] = self.0;
        let mut i = 2;
        while i < 16 {
            table[i] = mont_mul_limbs(table[i - 1], self.0);
            i += 1;
        }
        let mut acc = Self::ONE.0;
        // False until the leading non-zero window, so that a short exponent
        // costs no squaring of `ONE`.
        let mut started = false;
        let mut k = exp.len();
        while k > 0 {
            k -= 1;
            let limb = exp[k];
            let mut s = 16usize;
            while s > 0 {
                s -= 1;
                let d = ((limb >> (4 * s)) & 0xF) as usize;
                if started {
                    acc = sqr_n(acc, 4);
                    if d != 0 {
                        acc = mont_mul_limbs(acc, table[d]);
                    }
                } else if d != 0 {
                    acc = table[d];
                    started = true;
                }
            }
        }
        Fp256Mont(acc)
    }

    /// OS2IP mod `p` of a little-endian byte string of any length: Horner's
    /// method over 32-byte chunks, most significant chunk first, with each
    /// chunk reduced by one conditional subtraction and the chunk weight
    /// `2^256 mod p` supplied by [`Fp256Mont::TWO_POW_256`]. A 32-byte input
    /// costs no multiplication and the 48- and 64-byte inputs of
    /// `hash_to_field` cost one.
    fn from_bytes(bytes: &[u8]) -> Self {
        let n = (bytes.len() + 31) / 32;
        let mut acc = Self::ZERO;
        let mut k = n;
        while k > 0 {
            k -= 1;
            let start = 32 * k;
            let mut end = start + 32;
            if end > bytes.len() {
                end = bytes.len();
            }
            let mut buf = [0u8; 32];
            let mut i = start;
            while i < end {
                buf[i - start] = bytes[i];
                i += 1;
            }
            let chunk = Self::from_canonical_bytes(&buf);
            acc = acc.mul(Self::TWO_POW_256).add(chunk);
        }
        acc
    }

    /// The little-endian encoding of the canonical representative: out of the
    /// Montgomery domain, then out to bytes.
    fn to_bytes(self) -> [u8; 32] {
        limbs_to_bytes_le(self.to_canonical_limbs())
    }
}

impl ModArith for Fp256Mont {
    /// `a ↦ a·R`. On a representative `aR` this is `aR·R`, a Montgomery
    /// multiplication by `R^2`.
    fn to_mont(self) -> Self {
        Fp256Mont(mont_mul_limbs(self.0, R2_LIMBS))
    }

    /// `a ↦ a·R^{-1}`. On a representative `aR` this is `a`, a Montgomery
    /// multiplication by `1`.
    fn from_mont(self) -> Self {
        Fp256Mont(mont_mul_limbs(self.0, ONE_RAW))
    }

    /// `(a, b) ↦ a·b·R^{-1}`: the product of the two field values, then out
    /// of the domain once.
    fn mont_mul(self, rhs: Self) -> Self {
        self.mul(rhs).from_mont()
    }
}

impl CtField for Fp256Mont {
    fn ct_select(cond: u64, then_v: Self, else_v: Self) -> Self {
        Fp256Mont(select_limbs(mask_of(cond), then_v.0, else_v.0))
    }

    /// The or of the limb differences is zero exactly when the two canonical
    /// representatives agree; `x | (-x)` has its top bit set for every
    /// non-zero `x`.
    fn ct_eq(self, rhs: Self) -> u64 {
        let mut diff: u64 = 0;
        let mut i = 0;
        while i < 4 {
            diff |= self.0[i] ^ rhs.0[i];
            i += 1;
        }
        1 - ((diff | diff.wrapping_neg()) >> 63)
    }

    fn is_zero(self) -> u64 {
        self.ct_eq(Self::ZERO)
    }

    /// The parity of the representative in `[0, p)`, which is the parity of
    /// the low limb outside the Montgomery domain.
    fn is_negative(self) -> u64 {
        self.to_canonical_limbs()[0] & 1
    }

    fn ct_abs(self) -> Self {
        Self::ct_select(self.is_negative(), self.neg(), self)
    }
}

/// `sqrt_ratio_3mod4` (RFC 9380, Appendix F.2.1.2) at the P-256 prime with
/// `Z = -10`, the `Z` of the P-256 suites (Section 8.2).
impl SqrtRatio for Fp256Mont {
    const Z: Self = Fp256Mont(Z_MONT_LIMBS);

    fn sqrt_ratio(u: Self, v: Self) -> (u64, Self) {
        let c2: Self = Self::from_bytes(&SQRT_RATIO_3MOD4_C2_P256);
        // Step 1: tv1 = v^2.
        let tv1 = v.square();
        // Step 2: tv2 = u * v.
        let tv2 = u.mul(v);
        // Step 3: tv1 = tv1 * tv2.
        let tv1 = tv1.mul(tv2);
        // Step 4: y1 = tv1^c1, by the addition chain for c1 = (p - 3)/4.
        let y1 = Fp256Mont(pow_c1_limbs(tv1.0));
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

// --- differential tests against the num-bigint instance ------------------------

#[cfg(all(test, feature = "bigint-instances"))]
mod tests {
    use super::*;
    use crate::fp256::Fp256;
    use crate::sqrt::SQRT_RATIO_3MOD4_C1_P256;

    /// A deterministic SplitMix64 stream, so the randomized cases are the
    /// same on every run and the crate needs no `rand` dependency.
    struct SplitMix64 {
        state: u64,
    }

    impl SplitMix64 {
        fn new(seed: u64) -> Self {
            SplitMix64 { state: seed }
        }

        fn next_u64(&mut self) -> u64 {
            self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn next_bytes(&mut self, n: usize) -> Vec<u8> {
            let mut out = Vec::with_capacity(n);
            let mut i = 0;
            while i < n {
                out.push(self.next_u64() as u8);
                i += 1;
            }
            out
        }
    }

    fn le(limbs: [u64; 4]) -> [u8; 32] {
        limbs_to_bytes_le(limbs)
    }

    /// The little-endian 32-byte encodings the differential tests run over:
    /// the field edge cases plus the RFC constants.
    fn edge_cases() -> Vec<[u8; 32]> {
        vec![
            le([0, 0, 0, 0]),
            le([1, 0, 0, 0]),
            le([2, 0, 0, 0]),
            le([3, 0, 0, 0]),
            // p - 1, p - 2, and p itself (which reduces to 0).
            le([
                0xFFFF_FFFF_FFFF_FFFE,
                0x0000_0000_FFFF_FFFF,
                0x0000_0000_0000_0000,
                0xFFFF_FFFF_0000_0001,
            ]),
            le(P_MINUS_TWO),
            le(P_LIMBS),
            // 2^256 - 1: the largest 32-byte input, above p.
            le([
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
            ]),
            // R = 2^256 mod p, and R^2 mod p.
            le(R_LIMBS),
            le(R2_LIMBS),
            // Powers of two straddling the limb boundaries.
            le([0, 1, 0, 0]),
            le([0, 0, 1, 0]),
            le([0, 0, 0, 1]),
            le([0, 0, 0, 0x8000_0000_0000_0000]),
            // The sqrt constants of RFC 9380, Appendix F.2.1.2 for P-256.
            SQRT_RATIO_3MOD4_C2_P256,
            le([
                0xFFFF_FFFF_FFFF_FFF5,
                0x0000_0000_FFFF_FFFF,
                0x0000_0000_0000_0000,
                0xFFFF_FFFF_0000_0001,
            ]),
        ]
    }

    /// The edge cases followed by pseudorandom 32-byte inputs.
    fn sample_inputs(count: usize) -> Vec<[u8; 32]> {
        let mut out = edge_cases();
        let mut rng = SplitMix64::new(0x0123_4567_89AB_CDEF);
        let mut i = 0;
        while i < count {
            let mut b = [0u8; 32];
            let mut j = 0;
            while j < 4 {
                let w = rng.next_u64();
                let mut k = 0;
                while k < 8 {
                    b[8 * j + k] = (w >> (8 * k)) as u8;
                    k += 1;
                }
                j += 1;
            }
            out.push(b);
            i += 1;
        }
        out
    }

    fn fast(b: &[u8; 32]) -> Fp256Mont {
        Fp256Mont::from_bytes(b)
    }

    fn slow(b: &[u8; 32]) -> Fp256 {
        Fp256::from_bytes(b)
    }

    fn agree(tag: &str, a: Fp256Mont, b: Fp256) {
        assert_eq!(a.to_bytes(), b.to_bytes(), "{tag}");
    }

    // --- the constants -----------------------------------------------------

    #[test]
    fn modulus_limbs_match_the_crate_constant() {
        assert_eq!(P_LIMBS, crate::FIELD_MODULUS_P256);
    }

    #[test]
    fn n0inv_is_the_negated_inverse_of_p_mod_2_64() {
        // p·N0INV ≡ -1 (mod 2^64).
        assert_eq!(P_LIMBS[0].wrapping_mul(N0INV), u64::MAX);
    }

    #[test]
    fn r_is_two_to_the_256_mod_p() {
        // R = 2^256 - p, since p > 2^255.
        let (diff, borrow) = sub_limbs([0, 0, 0, 0], P_LIMBS);
        assert_eq!(borrow, 1);
        assert_eq!(diff, R_LIMBS);
    }

    #[test]
    fn one_is_r_and_encodes_as_one() {
        assert_eq!(Fp256Mont::ONE.0, R_LIMBS);
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(Fp256Mont::ONE.to_bytes(), expected);
        assert_eq!(Fp256Mont::ZERO.to_bytes(), [0u8; 32]);
    }

    #[test]
    fn r2_is_the_montgomery_form_of_r() {
        // Montgomery-multiplying R^2 by 1 leaves R, so R^2 represents R.
        assert_eq!(mont_mul_limbs(R2_LIMBS, ONE_RAW), R_LIMBS);
        // And R^2 is the square of R in the field.
        assert_eq!(Fp256Mont::TWO_POW_256, Fp256Mont::from_canonical_bytes(&le(R_LIMBS)));
    }

    #[test]
    fn z_constant_agrees_with_the_bigint_instance() {
        let z_fast = <Fp256Mont as SqrtRatio>::Z;
        let z_slow = <Fp256 as SqrtRatio>::Z;
        agree("Z", z_fast, z_slow);
    }

    // --- representation ----------------------------------------------------

    #[test]
    fn canonical_round_trip_through_bytes() {
        for b in sample_inputs(256) {
            agree("from_bytes", fast(&b), slow(&b));
            let x = fast(&b);
            assert_eq!(Fp256Mont::from_bytes(&x.to_bytes()), x);
            // Every representative is below p.
            let (_, borrow) = sub_limbs(x.0, P_LIMBS);
            assert_eq!(borrow, 1, "representative not canonical");
        }
    }

    #[test]
    fn montgomery_round_trip_is_the_identity() {
        for b in sample_inputs(256) {
            let x = fast(&b);
            assert_eq!(x.to_mont().from_mont(), x, "from_mont ∘ to_mont");
            assert_eq!(x.from_mont().to_mont(), x, "to_mont ∘ from_mont");
        }
    }

    #[test]
    fn montgomery_ops_agree_with_the_bigint_instance() {
        let inputs = sample_inputs(32);
        for a in &inputs {
            agree("to_mont", fast(a).to_mont(), slow(a).to_mont());
            agree("from_mont", fast(a).from_mont(), slow(a).from_mont());
            for b in &inputs {
                agree("mont_mul", fast(a).mont_mul(fast(b)), slow(a).mont_mul(slow(b)));
            }
        }
    }

    #[test]
    fn mont_mul_satisfies_the_trait_contract() {
        let inputs = sample_inputs(32);
        for a in &inputs {
            for b in &inputs {
                let (x, y) = (fast(a), fast(b));
                assert_eq!(x.to_mont().mont_mul(y.to_mont()), x.mul(y).to_mont());
            }
        }
    }

    // --- the carry paths of the multiply and the squaring ---------------------

    /// Canonical *representatives* chosen for the carry paths: the ends of the
    /// range, the largest value below `p`, single saturated limbs, and the
    /// limb patterns of `p` and `R`. A representative `L` denotes the field
    /// value `L·R^{-1}`, which is how the reference is built below.
    fn representative_edges() -> Vec<[u64; 4]> {
        vec![
            [0, 0, 0, 0],
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            // p - 1 and p - 2, the top of the range.
            [
                0xFFFF_FFFF_FFFF_FFFE,
                0x0000_0000_FFFF_FFFF,
                0x0000_0000_0000_0000,
                0xFFFF_FFFF_0000_0001,
            ],
            P_MINUS_TWO,
            // The largest representative whose every low limb is saturated:
            // its top limb is one below the top limb of p.
            [
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_0000_0000,
            ],
            [
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0x0000_0000_0000_0000,
            ],
            // One saturated limb at a time, and one set bit at a time.
            [0xFFFF_FFFF_FFFF_FFFF, 0, 0, 0],
            [0, 0xFFFF_FFFF_FFFF_FFFF, 0, 0],
            [0, 0, 0xFFFF_FFFF_FFFF_FFFF, 0],
            [0, 0, 0, 0xFFFF_FFFF_0000_0000],
            [0, 0, 0, 1],
            [0, 0, 0, 0x8000_0000_0000_0000],
            [0x8000_0000_0000_0000, 0, 0, 0],
            // The limb patterns the reduction is built around.
            R_LIMBS,
            R2_LIMBS,
            [0, 0x0000_0000_FFFF_FFFF, 0, 0],
            [0x0000_0000_FFFF_FFFF, 0, 0, 0],
        ]
    }

    /// The edge representatives followed by pseudorandom canonical ones.
    fn representative_sample(count: usize) -> Vec<[u64; 4]> {
        let mut out = representative_edges();
        let mut rng = SplitMix64::new(0x5EED_0F_CA_11_AB_1E);
        let mut i = 0;
        while i < count {
            let v = [
                rng.next_u64(),
                rng.next_u64(),
                rng.next_u64(),
                rng.next_u64(),
            ];
            out.push(reduce_once(v, 0));
            i += 1;
        }
        out
    }

    /// The reference element of the same field value as the representative
    /// `v`, namely `v·R^{-1}`.
    fn slow_of_representative(v: [u64; 4]) -> Fp256 {
        Fp256::from_bytes(&le(v)).from_mont()
    }

    #[test]
    fn the_chosen_representatives_are_canonical() {
        for v in representative_sample(64) {
            let (_, borrow) = sub_limbs(v, P_LIMBS);
            assert_eq!(borrow, 1, "representative {v:?} is not below p");
        }
    }

    /// Products and squares at the representative edges, against the
    /// `num-bigint` instance. These are the inputs that drive the carry out of
    /// the top word of the accumulator and the final conditional subtraction.
    #[test]
    fn representative_products_agree_with_the_bigint_instance() {
        let inputs = representative_sample(24);
        for a in &inputs {
            let (xa, ya) = (Fp256Mont(*a), slow_of_representative(*a));
            agree("square at an edge representative", xa.square(), ya.square());
            assert_eq!(xa.square(), xa.mul(xa), "square against mul at {a:?}");
            for b in &inputs {
                let (xb, yb) = (Fp256Mont(*b), slow_of_representative(*b));
                agree("mul at an edge representative", xa.mul(xb), ya.mul(yb));
                agree("add at an edge representative", xa.add(xb), ya.add(yb));
                agree("sub at an edge representative", xa.sub(xb), ya.sub(yb));
            }
        }
    }

    /// The ten-product squaring and the sixteen-product multiplication are two
    /// routes through two different reductions; they must not diverge on any
    /// input.
    #[test]
    fn squaring_agrees_with_multiplying_by_itself() {
        for b in sample_inputs(512) {
            let x = fast(&b);
            assert_eq!(x.square(), x.mul(x), "square against mul");
        }
        for v in representative_sample(256) {
            let x = Fp256Mont(v);
            assert_eq!(x.square(), x.mul(x), "square against mul at {v:?}");
        }
    }

    /// The conditional subtraction at both settings of the carry out of the
    /// top word. `reduce_once` takes an argument below `2p`, so at `hi = 1`
    /// the low half is below `2p - 2^256 = p - R` and the result is `lo + R`,
    /// since `R = 2^256 - p`.
    #[test]
    fn reduce_once_handles_the_carry_out_of_the_top_word() {
        let mut covered = 0;
        for v in representative_sample(64) {
            let (sum, carry) = add_limbs(v, R_LIMBS);
            assert_eq!(carry, 0, "lo + R stays in 256 bits for lo below p");
            let (_, below_p) = sub_limbs(sum, P_LIMBS);
            if below_p == 1 {
                assert_eq!(reduce_once(v, 1), sum, "reduce_once at hi = 1");
                covered += 1;
            }
            assert_eq!(reduce_once(v, 0), v, "reduce_once at hi = 0");
        }
        assert!(covered > 4, "the hi = 1 branch went unexercised");
        // p itself, the boundary at hi = 0.
        assert_eq!(reduce_once(P_LIMBS, 0), [0, 0, 0, 0]);
        // The largest argument the contract allows at hi = 1 is 2p - 1, whose
        // low half is p - R - 1 and whose reduction is p - 1.
        let (p_minus_r, borrow) = sub_limbs(P_LIMBS, R_LIMBS);
        assert_eq!(borrow, 0);
        let (top, borrow) = sub_limbs(p_minus_r, [1, 0, 0, 0]);
        assert_eq!(borrow, 0);
        let (p_minus_one, borrow) = sub_limbs(P_LIMBS, [1, 0, 0, 0]);
        assert_eq!(borrow, 0);
        assert_eq!(reduce_once(top, 1), p_minus_one, "reduce_once at 2p - 1");
    }

    // --- the ring operations ------------------------------------------------

    #[test]
    fn unary_ops_agree_with_the_bigint_instance() {
        for b in sample_inputs(128) {
            let (x, y) = (fast(&b), slow(&b));
            agree("neg", x.neg(), y.neg());
            agree("square", x.square(), y.square());
            agree("double", x.double(), y.double());
            agree("inv", x.inv(), y.inv());
        }
    }

    #[test]
    fn binary_ops_agree_with_the_bigint_instance() {
        let inputs = sample_inputs(48);
        for a in &inputs {
            for b in &inputs {
                let (xa, xb) = (fast(a), fast(b));
                let (ya, yb) = (slow(a), slow(b));
                agree("add", xa.add(xb), ya.add(yb));
                agree("sub", xa.sub(xb), ya.sub(yb));
                agree("mul", xa.mul(xb), ya.mul(yb));
            }
        }
    }

    #[test]
    fn inverse_is_a_two_sided_inverse() {
        for b in sample_inputs(256) {
            let x = fast(&b);
            if x == Fp256Mont::ZERO {
                assert_eq!(x.inv(), Fp256Mont::ZERO);
            } else {
                assert_eq!(x.mul(x.inv()), Fp256Mont::ONE);
            }
        }
    }

    /// Exponents chosen for the 4-bit window of [`Field::pow`]: the empty and
    /// zero exponents, exponents below one window, leading zero windows and
    /// leading zero limbs, interior zero windows, all-ones windows, and the
    /// two exponents of the field's own callers.
    fn window_exponents() -> Vec<Vec<u64>> {
        vec![
            // Nothing to walk.
            vec![],
            vec![0],
            vec![0, 0, 0, 0],
            // Shorter than one window.
            vec![1],
            vec![2],
            vec![15],
            // One full window, then one past it.
            vec![16],
            vec![17],
            // Fifteen leading zero windows inside a single limb.
            vec![0x0000_0000_0000_000F],
            vec![0x0000_0000_0000_00F0],
            // Leading zero limbs above a set bit, and a single bit at the top.
            vec![0xFFFF_FFFF_FFFF_FFFF, 0],
            vec![1, 0, 0, 0],
            vec![0, 0, 0, 1],
            vec![0, 0, 0, 0x8000_0000_0000_0000],
            // All-ones windows, one limb and four.
            vec![0xFFFF_FFFF_FFFF_FFFF],
            vec![
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
            ],
            // Interior zero windows, alternating and in runs.
            vec![0x0F0F_0F0F_0F0F_0F0F],
            vec![0xF0F0_0F0F_0000_F0F0, 0x0000_0000_FFFF_0000],
            // The exponents of inv and sqrt_ratio.
            SQRT_RATIO_3MOD4_C1_P256.to_vec(),
            P_MINUS_TWO.to_vec(),
        ]
    }

    #[test]
    fn pow_agrees_with_the_bigint_instance() {
        for b in sample_inputs(16) {
            for e in window_exponents() {
                agree("pow", fast(&b).pow(&e), slow(&b).pow(&e));
            }
        }
    }

    /// The addition chain of [`pow_c1_limbs`] and the generic window are two
    /// implementations of the same two exponents; the window is checked
    /// against `num-bigint` by `pow_agrees_with_the_bigint_instance`.
    #[test]
    fn the_addition_chain_agrees_with_the_generic_pow() {
        for b in sample_inputs(128) {
            let x = fast(&b);
            assert_eq!(
                Fp256Mont(pow_c1_limbs(x.0)),
                x.pow(&SQRT_RATIO_3MOD4_C1_P256),
                "chain at c1 = (p - 3)/4"
            );
            assert_eq!(x.inv(), x.pow(&P_MINUS_TWO), "chain at p - 2");
        }
    }

    /// `4·c1 + 3 = p`, the relation that makes the Fermat exponent `p - 2`
    /// two squarings and one multiplication past `c1`.
    #[test]
    fn four_c1_plus_three_is_the_modulus() {
        let c1 = SQRT_RATIO_3MOD4_C1_P256;
        let (two_c1, carry) = add_limbs(c1, c1);
        assert_eq!(carry, 0);
        let (four, carry) = add_limbs(two_c1, two_c1);
        assert_eq!(carry, 0);
        let (sum, carry) = add_limbs(four, [3, 0, 0, 0]);
        assert_eq!(carry, 0);
        assert_eq!(sum, P_LIMBS);
    }

    // --- byte strings longer and shorter than 32 bytes ------------------------

    #[test]
    fn from_bytes_agrees_on_other_lengths() {
        let mut rng = SplitMix64::new(0xFEDC_BA98_7654_3210);
        for len in [0usize, 1, 7, 16, 31, 33, 40, 48, 63, 64, 65, 96] {
            let mut trial = 0;
            while trial < 32 {
                let b = rng.next_bytes(len);
                assert_eq!(
                    Fp256Mont::from_bytes(&b).to_bytes(),
                    Fp256::from_bytes(&b).to_bytes(),
                    "from_bytes at length {len}"
                );
                trial += 1;
            }
        }
    }

    // --- the constant-time family --------------------------------------------

    #[test]
    fn ct_family_agrees_with_the_bigint_instance() {
        let inputs = sample_inputs(64);
        for a in &inputs {
            let (x, y) = (fast(a), slow(a));
            assert_eq!(x.is_zero(), y.is_zero(), "is_zero");
            assert_eq!(x.is_negative(), y.is_negative(), "is_negative");
            agree("ct_abs", x.ct_abs(), y.ct_abs());
            for b in &inputs {
                assert_eq!(x.ct_eq(fast(b)), y.ct_eq(slow(b)), "ct_eq");
            }
        }
        let (u, v) = (fast(&edge_cases()[3]), fast(&edge_cases()[2]));
        assert_eq!(Fp256Mont::ct_select(1, u, v), u);
        assert_eq!(Fp256Mont::ct_select(0, u, v), v);
    }

    // --- sqrt_ratio -----------------------------------------------------------

    #[test]
    fn sqrt_ratio_agrees_with_the_bigint_instance() {
        let inputs = sample_inputs(8);
        for a in &inputs {
            for b in &inputs {
                let vf = fast(b);
                if vf == Fp256Mont::ZERO {
                    continue;
                }
                let (bit_f, y_f) = Fp256Mont::sqrt_ratio(fast(a), vf);
                let (bit_s, y_s) = Fp256::sqrt_ratio(slow(a), slow(b));
                assert_eq!(bit_f, bit_s, "sqrt_ratio flag");
                agree("sqrt_ratio value", y_f, y_s);
            }
        }
    }

    #[test]
    fn sqrt_ratio_returns_a_root() {
        let inputs = sample_inputs(16);
        let z = <Fp256Mont as SqrtRatio>::Z;
        for a in &inputs {
            for b in &inputs {
                let (u, v) = (fast(a), fast(b));
                if v == Fp256Mont::ZERO {
                    continue;
                }
                let (is_qr, y) = Fp256Mont::sqrt_ratio(u, v);
                let lhs = y.square().mul(v);
                if is_qr == 1 {
                    assert_eq!(lhs, u, "y^2·v = u");
                } else {
                    assert_eq!(lhs, z.mul(u), "y^2·v = Z·u");
                }
            }
        }
    }
}
