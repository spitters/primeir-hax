//! Reference instance of [`ExtField`]: the tower `Fp2`, `Fp6`, `Fp12` over
//! the Mersenne prime `p = 2^31 − 1`.
//!
//! * [`Fp`] is `GF(p)` ([`Field`]).
//! * [`Fp2`] is `Fp[u]/(u² + 1)`; `−1` is not a square since `p ≡ 3 (mod 4)`.
//! * [`Fp6`] is `Fp2[v]/(v³ − ξ)` with `ξ = 2 + u` ([`XI`]).
//! * [`Fp12`] is `Fp6[w]/(w² − v)`.
//!
//! `ξ` is neither a square nor a cube in `Fp2`, so `v³ − ξ` is irreducible
//! over `Fp2` and `w² − v` over `Fp6`: the shape of the BN and BLS12 towers,
//! at a prime small enough that the arithmetic is plain `u64`. The tests check
//! `frobenius(a, DEGREE) == a` at every level, which holds only if each
//! quotient is a field of the stated degree.
//!
//! `Fp2::conj` and `Fp12::conj` are written out (`a + b·u ↦ a − b·u`, `a + b·w
//! ↦ a − b·w`) and `Fp2::frobenius` is `conj` at odd powers, so the law
//! `conj == frobenius(DEGREE / 2)` compares two independent computations at
//! `Fp12` and the law `frobenius(·, 1) == ·^p` two at `Fp2`. At `Fp6` and
//! `Fp12` `frobenius` is the `p`-th power iterated.
//!
//! The module is the opaque arithmetic leaf: it is gated out of the
//! extraction.

use crate::ext::ExtField;
use crate::Field;

/// `p = 2^31 − 1`.
pub const P: u64 = 0x7FFF_FFFF;

/// An element of `GF(2^31 − 1)`, stored as its representative in `[0, p)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub u64);

impl Fp {
    /// The residue of `n` modulo p.
    pub fn new(n: u64) -> Self {
        Fp(n % P)
    }

    fn pow_u64(self, mut e: u64) -> Self {
        let mut base = self;
        let mut acc = Fp(1);
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            e >>= 1;
        }
        acc
    }
}

impl Field for Fp {
    const ZERO: Self = Fp(0);
    const ONE: Self = Fp(1);
    const MODULUS_LE: &'static [u64] = &[P];
    const BYTES: usize = 4;

    fn add(self, rhs: Self) -> Self {
        Fp::new(self.0 + rhs.0)
    }
    fn sub(self, rhs: Self) -> Self {
        Fp::new(self.0 + P - rhs.0)
    }
    fn mul(self, rhs: Self) -> Self {
        Fp::new(self.0 * rhs.0)
    }
    fn neg(self) -> Self {
        Fp::new(P - self.0)
    }
    fn square(self) -> Self {
        self.mul(self)
    }
    fn double(self) -> Self {
        self.add(self)
    }
    fn inv(self) -> Self {
        // Fermat: a^(p−2).
        self.pow_u64(P - 2)
    }
    fn pow(self, exp: &[u64]) -> Self {
        let mut acc = Fp(1);
        let mut j = exp.len();
        while j > 0 {
            j -= 1;
            let limb = exp[j];
            let mut bit = 64;
            while bit > 0 {
                bit -= 1;
                acc = acc.mul(acc);
                if (limb >> bit) & 1 == 1 {
                    acc = acc.mul(self);
                }
            }
        }
        acc
    }
    fn from_bytes(bytes: &[u8]) -> Self {
        let mut acc = 0u64;
        let mut i = bytes.len();
        while i > 0 {
            i -= 1;
            acc = (acc * 256 + bytes[i] as u64) % P;
        }
        Fp(acc)
    }
    /// Four bytes: `p < 2^31`.
    fn write_bytes(self, out: &mut [u8]) {
        out[..4].copy_from_slice(&(self.0 as u32).to_le_bytes());
    }
}

/// `a^e` by square-and-multiply, for any level.
fn pow_ext<E: ExtField>(a: E, e: u64) -> E {
    let mut acc = E::ONE;
    let mut bit = 64;
    while bit > 0 {
        bit -= 1;
        acc = acc.square();
        if (e >> bit) & 1 == 1 {
            acc = acc.mul(a);
        }
    }
    acc
}

/// The `k`-th iterate of `a ↦ a^p`.
fn frobenius_by_pow<E: ExtField>(a: E, k: usize) -> E {
    let mut x = a;
    for _ in 0..(k % E::DEGREE) {
        x = pow_ext(x, P);
    }
    x
}

// --- Fp2 ---------------------------------------------------------------------

/// `c0 + c1·u` in `Fp[u]/(u² + 1)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2 {
    /// The coefficient of `1`.
    pub c0: Fp,
    /// The coefficient of `u`.
    pub c1: Fp,
}

impl Fp2 {
    /// `c0 + c1·u` from two integers, reduced.
    pub const fn new(c0: u64, c1: u64) -> Self {
        Fp2 {
            c0: Fp(c0 % P),
            c1: Fp(c1 % P),
        }
    }
}

/// `ξ = 2 + u`, neither a square nor a cube in `Fp2`.
pub const XI: Fp2 = Fp2::new(2, 1);

impl ExtField for Fp2 {
    type Base = Fp;
    const MODULUS_LE: &'static [u64] = &[P];
    const DEGREE: usize = 2;
    const ZERO: Self = Fp2::new(0, 0);
    const ONE: Self = Fp2::new(1, 0);
    const NONRESIDUE: Self = XI;

    fn lift(b: Fp) -> Self {
        Fp2 { c0: b, c1: Fp(0) }
    }
    fn add(self, rhs: Self) -> Self {
        Fp2 {
            c0: self.c0.add(rhs.c0),
            c1: self.c1.add(rhs.c1),
        }
    }
    fn sub(self, rhs: Self) -> Self {
        Fp2 {
            c0: self.c0.sub(rhs.c0),
            c1: self.c1.sub(rhs.c1),
        }
    }
    fn neg(self) -> Self {
        Fp2 {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }
    /// `(a0 + a1·u)(b0 + b1·u) = (a0·b0 − a1·b1) + (a0·b1 + a1·b0)·u`.
    fn mul(self, rhs: Self) -> Self {
        Fp2 {
            c0: self.c0.mul(rhs.c0).sub(self.c1.mul(rhs.c1)),
            c1: self.c0.mul(rhs.c1).add(self.c1.mul(rhs.c0)),
        }
    }
    fn square(self) -> Self {
        self.mul(self)
    }
    /// `(a − b·u) / (a² + b²)`.
    fn inv(self) -> Self {
        let n = self.c0.square().add(self.c1.square()).inv();
        Fp2 {
            c0: self.c0.mul(n),
            c1: self.c1.neg().mul(n),
        }
    }
    fn conj(self) -> Self {
        Fp2 {
            c0: self.c0,
            c1: self.c1.neg(),
        }
    }
    /// `u^p = −u` since `p ≡ 3 (mod 4)`, so the Frobenius is `conj` at odd
    /// powers and the identity at even ones.
    fn frobenius(self, power: usize) -> Self {
        if power % 2 == 1 {
            self.conj()
        } else {
            self
        }
    }
    fn mul_by_nonresidue(self) -> Self {
        // (a + b·u)(2 + u) = (2a − b) + (a + 2b)·u.
        Fp2 {
            c0: self.c0.double().sub(self.c1),
            c1: self.c0.add(self.c1.double()),
        }
    }
}

// --- Fp6 ---------------------------------------------------------------------

/// `c0 + c1·v + c2·v²` in `Fp2[v]/(v³ − ξ)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6 {
    /// The coefficient of `1`.
    pub c0: Fp2,
    /// The coefficient of `v`.
    pub c1: Fp2,
    /// The coefficient of `v²`.
    pub c2: Fp2,
}

impl ExtField for Fp6 {
    type Base = Fp2;
    const MODULUS_LE: &'static [u64] = &[P];
    const DEGREE: usize = 6;
    const ZERO: Self = Fp6 {
        c0: Fp2::new(0, 0),
        c1: Fp2::new(0, 0),
        c2: Fp2::new(0, 0),
    };
    const ONE: Self = Fp6 {
        c0: Fp2::new(1, 0),
        c1: Fp2::new(0, 0),
        c2: Fp2::new(0, 0),
    };
    /// `v`.
    const NONRESIDUE: Self = Fp6 {
        c0: Fp2::new(0, 0),
        c1: Fp2::new(1, 0),
        c2: Fp2::new(0, 0),
    };

    fn lift(b: Fp2) -> Self {
        Fp6 {
            c0: b,
            c1: Fp2::ZERO,
            c2: Fp2::ZERO,
        }
    }
    fn add(self, rhs: Self) -> Self {
        Fp6 {
            c0: self.c0.add(rhs.c0),
            c1: self.c1.add(rhs.c1),
            c2: self.c2.add(rhs.c2),
        }
    }
    fn sub(self, rhs: Self) -> Self {
        Fp6 {
            c0: self.c0.sub(rhs.c0),
            c1: self.c1.sub(rhs.c1),
            c2: self.c2.sub(rhs.c2),
        }
    }
    fn neg(self) -> Self {
        Fp6 {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
            c2: self.c2.neg(),
        }
    }
    /// The schoolbook product, reducing `v³ = ξ`.
    fn mul(self, rhs: Self) -> Self {
        let (a0, a1, a2) = (self.c0, self.c1, self.c2);
        let (b0, b1, b2) = (rhs.c0, rhs.c1, rhs.c2);
        Fp6 {
            c0: a0
                .mul(b0)
                .add(a1.mul(b2).add(a2.mul(b1)).mul_by_nonresidue()),
            c1: a0
                .mul(b1)
                .add(a1.mul(b0))
                .add(a2.mul(b2).mul_by_nonresidue()),
            c2: a0.mul(b2).add(a1.mul(b1)).add(a2.mul(b0)),
        }
    }
    fn square(self) -> Self {
        self.mul(self)
    }
    /// The inverse in a cubic extension `v³ = ξ`: with
    /// `A = a0² − ξ·a1·a2`, `B = ξ·a2² − a0·a1`, `C = a1² − a0·a2` and
    /// `F = a0·A + ξ·(a2·B + a1·C)`, the inverse is `(A + B·v + C·v²) / F`.
    fn inv(self) -> Self {
        let (a0, a1, a2) = (self.c0, self.c1, self.c2);
        let a = a0.square().sub(a1.mul(a2).mul_by_nonresidue());
        let b = a2.square().mul_by_nonresidue().sub(a0.mul(a1));
        let c = a1.square().sub(a0.mul(a2));
        let f = a0
            .mul(a)
            .add(a2.mul(b).add(a1.mul(c)).mul_by_nonresidue())
            .inv();
        Fp6 {
            c0: a.mul(f),
            c1: b.mul(f),
            c2: c.mul(f),
        }
    }
    fn conj(self) -> Self {
        self.frobenius(3)
    }
    fn frobenius(self, power: usize) -> Self {
        frobenius_by_pow(self, power)
    }
    /// `(c0 + c1·v + c2·v²)·v = ξ·c2 + c0·v + c1·v²`.
    fn mul_by_nonresidue(self) -> Self {
        Fp6 {
            c0: self.c2.mul_by_nonresidue(),
            c1: self.c0,
            c2: self.c1,
        }
    }
}

// --- Fp12 --------------------------------------------------------------------

/// `c0 + c1·w` in `Fp6[w]/(w² − v)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp12 {
    /// The coefficient of `1`.
    pub c0: Fp6,
    /// The coefficient of `w`.
    pub c1: Fp6,
}

impl ExtField for Fp12 {
    type Base = Fp6;
    const MODULUS_LE: &'static [u64] = &[P];
    const DEGREE: usize = 12;
    const ZERO: Self = Fp12 {
        c0: Fp6::ZERO,
        c1: Fp6::ZERO,
    };
    const ONE: Self = Fp12 {
        c0: Fp6::ONE,
        c1: Fp6::ZERO,
    };
    /// `w`.
    const NONRESIDUE: Self = Fp12 {
        c0: Fp6::ZERO,
        c1: Fp6::ONE,
    };

    fn lift(b: Fp6) -> Self {
        Fp12 {
            c0: b,
            c1: Fp6::ZERO,
        }
    }
    fn add(self, rhs: Self) -> Self {
        Fp12 {
            c0: self.c0.add(rhs.c0),
            c1: self.c1.add(rhs.c1),
        }
    }
    fn sub(self, rhs: Self) -> Self {
        Fp12 {
            c0: self.c0.sub(rhs.c0),
            c1: self.c1.sub(rhs.c1),
        }
    }
    fn neg(self) -> Self {
        Fp12 {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }
    /// `(a0 + a1·w)(b0 + b1·w) = (a0·b0 + v·a1·b1) + (a0·b1 + a1·b0)·w`.
    fn mul(self, rhs: Self) -> Self {
        Fp12 {
            c0: self
                .c0
                .mul(rhs.c0)
                .add(self.c1.mul(rhs.c1).mul_by_nonresidue()),
            c1: self.c0.mul(rhs.c1).add(self.c1.mul(rhs.c0)),
        }
    }
    fn square(self) -> Self {
        self.mul(self)
    }
    /// `(a − b·w) / (a² − v·b²)`.
    fn inv(self) -> Self {
        let d = self
            .c0
            .square()
            .sub(self.c1.square().mul_by_nonresidue())
            .inv();
        Fp12 {
            c0: self.c0.mul(d),
            c1: self.c1.mul(d).neg(),
        }
    }
    fn conj(self) -> Self {
        Fp12 {
            c0: self.c0,
            c1: self.c1.neg(),
        }
    }
    fn frobenius(self, power: usize) -> Self {
        frobenius_by_pow(self, power)
    }
    /// `(c0 + c1·w)·w = v·c1 + c0·w`.
    fn mul_by_nonresidue(self) -> Self {
        Fp12 {
            c0: self.c1.mul_by_nonresidue(),
            c1: self.c0,
        }
    }
}
