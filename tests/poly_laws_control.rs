//! A control on the law suite: four instances that break one law each, and the
//! suite rejects all four.
//!
//! Each is the `mlkem_q` instance with one operation replaced by a plausible
//! wrong one — the entry-wise product in NTT form (right for a complete
//! transform, wrong for ML-KEM's incomplete one), a scalar multiply that drops
//! its scalar, an inverse transform that drops the `128⁻¹` factor, and a
//! difference in NTT form taken in the other direction.

use primeir_hax::mlkem_q::{Fq, NttKem, PolyKem};
use primeir_hax::poly::PolyRing;
use primeir_hax::poly_laws::check_poly_ring;
use primeir_hax::Field;

/// `mlkem_q` with fault `FAULT` injected: 1 = entry-wise `basemul`,
/// 2 = `poly_smul` drops its scalar, 3 = `intt` drops the `128⁻¹` factor,
/// 4 = `ntt_sub` subtracts in the other direction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Mutant<const FAULT: u8>(PolyKem);

impl<const FAULT: u8> PolyRing for Mutant<FAULT> {
    type Coeff = Fq;
    type NttForm = NttKem;
    const N: usize = 256;
    const ZERO: Self = Mutant(PolyKem([0u16; 256]));
    const NTT_ZERO: NttKem = PolyKem::NTT_ZERO;

    fn coeff(self, i: usize) -> Fq {
        self.0.coeff(i)
    }
    fn with_coeff(self, i: usize, c: Fq) -> Self {
        Mutant(self.0.with_coeff(i, c))
    }
    fn ntt_coeff(w: NttKem, i: usize) -> Fq {
        PolyKem::ntt_coeff(w, i)
    }
    fn with_ntt_coeff(w: NttKem, i: usize, c: Fq) -> NttKem {
        PolyKem::with_ntt_coeff(w, i, c)
    }
    fn ntt(self) -> NttKem {
        self.0.ntt()
    }
    fn intt(w: NttKem) -> Self {
        let p = PolyKem::intt(w);
        if FAULT == 3 {
            Mutant(p.poly_smul(Fq(128)))
        } else {
            Mutant(p)
        }
    }
    fn basemul(a: NttKem, b: NttKem) -> NttKem {
        if FAULT == 1 {
            let mut w = NttKem([[0u16; 2]; 128]);
            for i in 0..256 {
                let c = PolyKem::ntt_coeff(a, i).mul(PolyKem::ntt_coeff(b, i));
                w.0[i >> 1][i & 1] = c.0;
            }
            w
        } else {
            PolyKem::basemul(a, b)
        }
    }
    fn ntt_add(a: NttKem, b: NttKem) -> NttKem {
        PolyKem::ntt_add(a, b)
    }
    fn ntt_sub(a: NttKem, b: NttKem) -> NttKem {
        if FAULT == 4 {
            PolyKem::ntt_sub(b, a)
        } else {
            PolyKem::ntt_sub(a, b)
        }
    }
    fn poly_add(self, rhs: Self) -> Self {
        Mutant(self.0.poly_add(rhs.0))
    }
    fn poly_sub(self, rhs: Self) -> Self {
        Mutant(self.0.poly_sub(rhs.0))
    }
    fn poly_smul(self, c: Fq) -> Self {
        if FAULT == 2 {
            self
        } else {
            Mutant(self.0.poly_smul(c))
        }
    }
    fn ntt_mul(self, rhs: Self) -> Self {
        Self::intt(Self::basemul(self.ntt(), rhs.ntt()))
    }
}

fn suite_rejects<const FAULT: u8>() -> bool {
    std::panic::catch_unwind(|| check_poly_ring::<Mutant<FAULT>>("mutant", 0x1234, 1)).is_err()
}

#[test]
fn the_law_suite_rejects_a_broken_instance() {
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let verdict = [
        suite_rejects::<1>(),
        suite_rejects::<2>(),
        suite_rejects::<3>(),
        suite_rejects::<4>(),
    ];
    std::panic::set_hook(hook);
    assert_eq!(
        verdict,
        [true, true, true, true],
        "the law suite accepted a broken instance (entry-wise basemul, \
         scalar-dropping poly_smul, unscaled intt, reversed ntt_sub)"
    );
}
