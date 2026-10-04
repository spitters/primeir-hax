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
| `Field` | field arithmetic and its derived forms; the modulus `MODULUS_LE` and the byte codec `BYTES`, `from_bytes`, `write_bytes` |
| `ModArith` | `to_mont`, `from_mont`, `mont_mul` |
| `poly::PolyRing` | `ntt`, `intt`, `basemul`, `basemul_acc`, and the ring operations in both forms |
| `EcGroup` | `point_add`, `point_double`, `scalar_mul` |
| `ct::CtField` | `ct_select`, `ct_eq`, `is_zero`, `is_negative`, `ct_abs` |
| `sqrt::SqrtRatio` | `sqrt_ratio` (RFC 9380, Appendix F.2.1) |
| `ext::ExtField` | one level of a tower (`Fp2`, `Fp6`, `Fp12`): `mul`, `square`, `inv`, `conj`, `frobenius`, `mul_by_nonresidue`, `lift` |
| `binary::BinaryField` | `GF(2^n)`: `gf_add`, `gf_mul`, `ghash_step`, `polyval_step` |
| `rounding::Rounding` | `compress_d`, `decompress_d` (FIPS 203); `power2round`, `decompose`, `high_bits`, `low_bits`, `make_hint`, `use_hint` (FIPS 204) |

Reference instances: `fp25519` (Curve25519 base field, with edwards25519),
`fp256` (NIST P-256 base field), `mldsa_q` (`q = 8380417`, FIPS 204),
`mlkem_q` (`q = 3329`, FIPS 203), `ext_ref` (the tower `Fp2`/`Fp6`/`Fp12`
over `2^31 − 1`) and `gf128` (GF(2^128) at the GHASH and POLYVAL moduli).
`src/laws.rs` states each law once as a Boolean function; the tests assert
the laws at every instance.

## Name manifest

`names.toml` lists each trait item a compiler recognises by name: its
qualified def path, its arity and its op key (`field.mul`, `ring.basemul_acc`,
`tower.frobenius`, ...). It is the interface between the library and the
compiler. `tests/names_manifest.rs` checks each entry against the trait
declarations in `src/` and, when `hax_frontend_export.json` is present,
against the def paths of the export: `[[extracted]]` entries must appear in
it, `[[pending]]` entries (added since the export was taken) must not, and
move to `[[extracted]]` after a re-extraction.

## Features and extraction

`fp256_mont`, the fixed-width P-256 field, is not part of the compiler's
input. Under rustc `fixed-width-instances` enables it; an extraction carries
it only with `fieldmodel-witness`, for the export behind the `FieldModel`
witness:

```
cargo hax json                                          # the compiler's input
cargo hax -C --features fieldmodel-witness \; json      # the FieldModel witness
```

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
