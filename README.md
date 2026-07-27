# Narya Ed25519 Assembly

Standalone AMD64 assembly for Narya's eight-lane Ed25519 verification design.
The library is building toward a stable System V C ABI and has no Go runtime,
cgo, or language-runtime dependency. It is intended to make the optimized
arithmetic usable—and independently auditable—from C, C++, Rust, Zig, and
validator clients that cannot embed the Go package.

> [!WARNING]
> This repository is alpha, incomplete, and unaudited. The current checkpoint
> contains independently tested verifier components, not a complete signature
> verifier. Do not use it to make security or consensus decisions.

The ABI version is currently zero and may change without compatibility shims.
ABI stability starts only after the complete strict verifier and its audit
boundary are frozen.

## Status

- Implemented: runtime CPU/OS feature gate; checked r51×8 multiply, add,
  subtract, and negate; SysV AMD64 IFMA leaves; extended-point doubling and
  projective-Niels mixed addition; portable bit-exact differential oracles;
  permissive compressed-point decompression; x8 rolling-register SHA-512
  compression and exact segmented verifier hashing; x8 canonical scalar
  reduction and exact signed radix-32 recoding; pre-signed projective-Niels
  tables and the micro-AoS transpose selector; full-width x8 variable-base
  scalar multiplication; alias, lane-independence, known-answer, and range
  tests.
- In progress: paired A/R decode scheduling, strict byte prechecks,
  fixed-base multiplication, assembly of the complete Straus equation, strict
  final predicate, and lane verdict mapping.
- Supported verification target: eight independent cold Ed25519 equations
  under Narya's `DalekStrict` acceptance predicate. Automatic or aggregate
  randomized verification is not part of this design.

## Build and test

On a Linux AMD64 machine with AVX-512 IFMA:

```sh
make
make test
make test-native
make test-sanitize
```

`make check-source` asks Clang to parse the GNU assembly for an x86-64 ELF
target and is useful on a non-x86 development host.

## Audit orientation

The assembly is intentionally heavily commented. Each leaf records:

- its exact SysV register and memory ABI;
- field representation and machine-range preconditions;
- why every modular fold is exact and cannot wrap;
- whether inputs and outputs may alias;
- which instructions preserve lane independence;
- the source Narya commit whose representation it must match.

The field proof obligations are collected in
[`docs/proofs/R51_FIELD_CONTRACT.md`](docs/proofs/R51_FIELD_CONTRACT.md), and
the signed scalar-reduction boundary is documented in
[`docs/proofs/SCALAR_REDUCTION_CONTRACT.md`](docs/proofs/SCALAR_REDUCTION_CONTRACT.md).
Candidate machine-checked work is recorded in
[`docs/proofs/FORMALIZATION_BACKLOG.md`](docs/proofs/FORMALIZATION_BACKLOG.md).
The implementation boundary is described in
[`docs/architecture/PORTING_PLAN.md`](docs/architecture/PORTING_PLAN.md).
The [documentation index](docs/README.md) separates architecture, proofs,
audit material, performance reports, and raw reproducibility evidence.

## License and attribution

Apache-2.0. See `NOTICE` for exact implementation provenance. The standalone
r51×8 kernel is translated from Narya's independently implemented Go-ABI
assembly; it does not include the separate Firedancer-derived r43x6 reference
backend.
