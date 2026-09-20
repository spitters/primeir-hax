# primeir-hax

A stable-Rust trait surface for prime-field, modular, polynomial-ring and
elliptic-curve arithmetic, written so that an extraction tool can recognize a
call by trait and method name rather than by reconstructing the operation from
limb-and-loop code.

The traits are ordinary Rust with working reference instances, so `cargo test`
runs genuine arithmetic. Under [hax](https://github.com/cryspen/hax) the trait
surface extracts on its own; the instance bodies are opaque leaves.

| Trait | Operations |
|---|---|
| `Field` | field arithmetic and its derived forms |
| `ModArith` | `to_mont`, `from_mont`, `mont_mul`, `mont_inverse` |
| `poly::PolyRing` | `ntt`, `intt`, `basemul`, and the ring operations in both forms |
| `EcGroup` | `point_add`, `point_double`, `scalar_mul` |
| `ct::CtField` | `ct_select`, `ct_eq`, `is_zero`, `is_negative`, `ct_abs` |
| `sqrt::SqrtRatio` | `sqrt_ratio` (RFC 9380, Appendix F.2.1) |

Reference instances: `fp25519` (Curve25519 base field, with edwards25519),
`fp256` (NIST P-256 base field), `mldsa_q` (`q = 8380417`, FIPS 204) and
`mlkem_q` (`q = 3329`, FIPS 203).

The scalar of `EcGroup::scalar_mul` is secret, carried as `Scalar`, whose only
escape is `Scalar::declassify`.

```
cargo test
cargo test --features fixed-width-instances
```

Without the default `bigint-instances` feature the crate is the trait surface
plus the lattice instances, is `no_std`, and has no dependencies.

Test vectors and their provenance are recorded per test file in
`validation.toml`.

MIT licensed.
