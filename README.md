# primeir-hax

The prime-IR trait surface: a stable-Rust, nominally recognizable vocabulary for
prime-field, modular, polynomial-ring and elliptic-curve arithmetic. Each trait
method is named after the compiler dialect operation it maps to, so an extraction
can recognize a call by trait and method name rather than by reconstructing the
operation's identity from limb-and-loop code.

The crate is dual-use. Under `rustc` the traits are ordinary Rust with working
reference instances, so `cargo test` runs genuine arithmetic; there are no
intrinsics and no nightly features. Under [hax](https://github.com/cryspen/hax),
`cargo hax into lean` extracts the *trait surface* alone — the instance bodies
are opaque arithmetic leaves whose implementation is supplied elsewhere and tied
by value.

Unlike the per-standard crates it supports, this one implements no standard end
to end. It is the shared vocabulary those crates are written against.

## Standards

- RFC 8032, *EdDSA*, for the edwards25519 published constants: the base point
  `B`, the curve parameter `d`, and the prime subgroup order
  `L = 2^252 + 27742317777372353535851937790883648493`.
- RFC 9496, *Ristretto255 and Decaf448*, Appendix A, for the constant-time
  field operations.
- RFC 9380, *Hashing to Elliptic Curves*, Appendix F.2.1, for the
  square-root-of-a-ratio operation.
- FIPS 204 (ML-DSA) Table 1, §7.5, Algorithm 42 and Appendix B, for the
  `q = 8380417` instance and its complete 8-layer transform.
- FIPS 203 (ML-KEM) §4.3 and Algorithms 9–12, for the `q = 3329` instance and
  its incomplete 7-layer transform.

## Trait families

| Family | Trait | Operations |
|---|---|---|
| Field | `Field` | the field operations and their derived forms |
| Modular | `ModArith` | the Montgomery domain: `to_mont`, `from_mont`, `mont_mul`, `mont_inverse` |
| Polynomial ring | `poly::PolyRing` | `ntt`, `intt`, `basemul`, `ntt_add`, `ntt_sub`, `poly_add`, `poly_sub`, `poly_smul`, `ntt_mul`, and construction of an element in NTT form entry by entry |
| Elliptic curve | `EcGroup` | `point_add`, `point_double`, `scalar_mul` |
| Constant time | `ct::CtField` | `ct_select`, `ct_eq`, `is_zero`, `is_negative`, `ct_abs` |
| Square root of a ratio | `sqrt::SqrtRatio` | `sqrt_ratio` |

The scalar of `EcGroup::scalar_mul` is secret, carried as the newtype `Scalar`
whose only escape is the audited `Scalar::declassify`. The secrecy marker is in
the type, recognized at the same site as `secret_integers`.

## Reference instances

| Instance | Modulus | Families |
|---|---|---|
| `fp25519` | `2^255 - 19` | `Field`, `ModArith`, `EcGroup`, `CtField`, `SqrtRatio` |
| `fp256` | the NIST P-256 base field | `Field`, `ModArith`, `CtField`, `SqrtRatio` |
| `mldsa_q` | `8380417` | `Field`, `ModArith`, `PolyRing` |
| `mlkem_q` | `3329` | `Field`, `PolyRing` |

An instance may be realized by a bignum library, by fiat-crypto, or by a verified
compiler emitting Rust; the trait declares the leaf's identity and the
realization is interchangeable. The instances here are the reference ones, so
that the surface compiles and the vector tests run.

## Features

| Feature | Default | Effect |
|---|---|---|
| `bigint-instances` | on | the `num-bigint`-backed `fp25519` and `fp256` instances. Without it the crate is the trait surface plus `mldsa_q`, is `no_std`, and has no dependency, so a `no_std` crate can implement the traits. |
| `fixed-width-instances` | off | `fp256_mont`, the P-256 base field as four `u64` Montgomery limbs, with no allocation and no dependency. Its differential tests compare it against `fp256` and so need `bigint-instances` too. |
| `cross-check` | off | the two lattice cross-check test files, and the `mldsa-hax` and `mlkem-hax` dependencies they compare against. |

## Test vectors and their provenance

| File | Source | Coverage |
|---|---|---|
| `tests/kat.rs` | RFC 8032 published constants; `num-bigint` as an independent reference | field identities, the Montgomery contract, and the group law at `[L]B = O` and `[L+1]B = B` |
| `tests/ct_properties.rs` | RFC 9496, Appendix A.2 | the eight published negative field elements through `is_negative` and `ct_abs` |
| `tests/poly_laws_control.rs` | none — a negative control | four instances each breaking one law, which the generic suite must reject |
| `tests/lattice_kat.rs` | FIPS 204; `mldsa-hax` as an independent reference | the zetas table, the field operations, `ntt` / `intt` / `basemul`, and the definition of the transform by Horner evaluation |
| `tests/mlkem_lattice_kat.rs` | FIPS 203; `mlkem-hax` as an independent reference | the constants, the field operations, the ordering of the incomplete transform, and that `basemul` is 128 independent degree-1 products |

The RFC 8032 and RFC 9496 values were copied from the published documents; their
provenance is recorded per test file in `validation.toml`.

`src/poly_laws.rs` is the law suite of the lattice surface as generic checks —
the transform's bijectivity, the ring operations transported along it, the ring
axioms, and the generic callers — which both lattice instances pass on
pseudorandom inputs, and which `poly_laws_control.rs` shows to be discriminating.

The last two files compare against `mldsa-hax` and `mlkem-hax`, independent
implementations of FIPS 204 and FIPS 203 validated against the NIST ACVP and
ML-KEM-768 vectors. Those two crates are not part of this repository, so the
files are behind the `cross-check` feature and a default `cargo test` does not
run them.

## Running the tests

```
cargo test --release
cargo test --release --features fixed-width-instances
cargo clippy
cargo doc --no-deps
```

The cross-checks additionally need `mldsa-hax` and `mlkem-hax` available:

```
cargo test --release --features cross-check
```

## hax extraction

`cargo hax into lean` extracts the trait surface. The instance bodies are gated
out of the extraction with `#[cfg(not(hax))]`, so the surface extracts even
though `num-bigint` is outside hax's input subset.
