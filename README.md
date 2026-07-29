# Narya Ed25519 Assembly

Standalone AMD64 assembly for Narya's eight-lane Ed25519 verification design.
The library is building toward a stable System V C ABI and has no Go runtime,
cgo, or language-runtime dependency. It is intended to make the optimized
arithmetic usable—and independently auditable—from C, C++, Rust, Zig, and
validator clients that cannot embed the Go package.

> [!WARNING]
> This repository is alpha, incomplete, and unaudited. The current checkpoint
> contains a complete but not yet performance-final strict verifier. Do not
> use it to make security or consensus decisions.

The ABI version is currently zero and may change without compatibility shims.
ABI stability starts only after the complete strict verifier and its audit
boundary are frozen.

## Status

- Implemented: runtime CPU/OS feature gate; checked r51×8 multiply, add,
  subtract, and negate; SysV AMD64 IFMA leaves; a register-resident decoder
  square chain; fused raw-product/direct-XY doubling Stage-2; typed P2/P3
  intermediate doubling; fused projective- and affine-Niels Stage-2 leaves;
  portable bit-exact differential oracles;
  permissive compressed-point decompression; x8 rolling-register SHA-512
  compression and exact segmented verifier hashing; x8 canonical scalar
  reduction and exact signed radix-32 recoding; pre-signed projective-Niels
  tables and the micro-AoS transpose selector; full-width x8 variable-base
  scalar multiplication; an immutable radix-256 basepoint comb with a masked
  affine-Niels transpose leaf; the complete x8 `DalekStrict` equation and
  public workspace ABI; alias, lane-independence, known-answer, and range
  tests; and a machine-checked Lean scalar trace generated from the radix-51
  IFMA multiply source, including the exact product order and register route,
  per-instruction no-wrap, fold, carry, modular result, and reusable-range
  lemmas.
- Implemented assurance hardening: the scalar reducer's exact 60-macro
  register route is fail-closed and mutation-tested; its 389 signed
  intermediates are source-certified, and a Lean canonical-tail theorem proves
  the reconstructed result lies in `[0,l)` under the documented parser bounds.
- In progress: long native fuzzing, broader performance characterization, and
  further formal refinement. The
  checked-in external corpus covers RFC 8032, CCTV, Wycheproof, and derived
  predicate-boundary cases.
- Supported verification target: eight independent cold Ed25519 equations
  under Narya's `DalekStrict` acceptance predicate. Automatic or aggregate
  randomized verification is not part of this design.

## Repository map

The top-level directories follow the assurance boundary rather than the order
in which the implementation was written:

- `include/` — the public, versioned C ABI;
- `src/` — C orchestration and GNU/System V AMD64 assembly leaves;
- `tests/` — native differentials, adversarial cases, and committed vectors;
- `formal/lean/` — machine-checked algebra and arithmetic traces;
- `docs/architecture/` — representations, algorithms, and ABI decisions;
- `docs/proofs/` — proved claims, trust boundaries, and formalization backlog;
- `docs/audits/` — reviewer scope and security-facing material;
- `docs/performance/` — benchmark methodology, not correctness evidence; and
- `docs/reproducibility/` — immutable machine outputs and checksums.

Start with the [documentation index](docs/README.md). External arithmetic
implementers should begin with the
[field-arithmetic evidence handoff](docs/proofs/FIELD_ARITHMETIC_HANDOFF.md);
reviewers of the complete verifier should begin with the
[auditor quickstart](docs/audits/AUDITOR_QUICKSTART.md) and then the
[audit scope](docs/audits/AUDIT_SCOPE.md).

## Build and test

On a Linux AMD64 machine with AVX-512 IFMA:

```sh
make
make test
make test-native
make test-sanitize
make check-generated
make formal-check
```

`make check-source` asks Clang to parse the GNU assembly for an x86-64 ELF
target and is useful on a non-x86 development host.

`make formal-check` uses the pinned Lean/mathlib project under `formal/lean`.
It first regenerates and compares the multiply leaf's source trace, then proves
the arithmetic and range theorem over that generated output. It also rebuilds
a deterministic linked ELF, decodes the exact 800-byte multiplier symbol with
a fail-closed restricted x86-64 decoder, and proves that the result is the
independently source-generated 129-instruction trace. The exact decoded program
also executes in the unbounded-natural shadow semantics to the independently
generated radix-51 result. The decoded 94-instruction arithmetic core also has
a fault-aware BitVec-to-Nat lane-refinement theorem with explicit range and
linked-constant memory premises. A relational execution theorem proves that
arbitrary caller values in ZMM28--31 cannot affect its five outputs. The five
decoded output stores separately have permission-sensitive row/lane read-back
and isolation theorems; the exact ten-load/eighteen-clear prefix now separately
establishes the arithmetic precondition from explicit readable input rows. A
single theorem now composes the entire decoded multiplier leaf with no
source/output disjointness premise, retains its exact output frame, preserves
a disjoint entry return word through the stores, and proves the decoded
`VZEROUPPER; RET`, RSP+8, and return-RIP effects. Downstream deployment
identity, wrapper/dispatch refinement, concurrent mutation, and correspondence
to physical CPU behavior remain explicit open boundaries.

Hosted CI builds with GCC and Clang, parses every assembly leaf, reproduces
generated artifacts, validates the external corpus, builds the fuzz target,
and checks the Lean project. The separately dispatched native workflow is
pinned to a self-hosted runner labeled `narya-ifma`; it runs the real native,
sanitizer, and fuzz gates. Hosted or emulated success is never presented as a
native performance result.

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
the concise external evidence map is
[`docs/proofs/FIELD_ARITHMETIC_HANDOFF.md`](docs/proofs/FIELD_ARITHMETIC_HANDOFF.md).
The checked Lean source is under [`formal/lean`](formal/lean/README.md). The
[source-refinement certificate](docs/proofs/R51_SOURCE_TRACE_REFINEMENT.md)
explains how multiply assembly edits reach the theorem; the same fail-closed
source link and modular/range proofs now cover add, subtract, and negate. The
[x86 execution/ABI evidence and remaining trust boundary](docs/proofs/X86_OBJECT_REFINEMENT_PLAN.md)
are specified separately. The
signed scalar-reduction boundary is documented in
[`docs/proofs/SCALAR_REDUCTION_CONTRACT.md`](docs/proofs/SCALAR_REDUCTION_CONTRACT.md).
The independent 2026-07-28 review finding, remediation, and remaining trust
boundary are recorded in
[`docs/audits/SCALAR_REDUCTION_REVIEW_2026-07-28.md`](docs/audits/SCALAR_REDUCTION_REVIEW_2026-07-28.md).
The complete acceptance predicate and its equivalence obligations are in
[`docs/architecture/STRICT_PREDICATE.md`](docs/architecture/STRICT_PREDICATE.md).
Candidate machine-checked work is recorded in
[`docs/proofs/FORMALIZATION_BACKLOG.md`](docs/proofs/FORMALIZATION_BACKLOG.md).
The implementation boundary is described in
[`docs/architecture/PORTING_PLAN.md`](docs/architecture/PORTING_PLAN.md).
The promoted point schedule and its P2/P3 type boundary are described in
[`docs/architecture/POINT_DOUBLING.md`](docs/architecture/POINT_DOUBLING.md).
The bounded mixed-addition boundary is described in
[`docs/architecture/NIELS_ADDITION.md`](docs/architecture/NIELS_ADDITION.md).
The [documentation index](docs/README.md) separates architecture, proofs,
audit material, performance reports, and raw reproducibility evidence.

## License and attribution

Apache-2.0. See `NOTICE` for exact implementation provenance. The standalone
r51×8 kernel is translated from Narya's independently implemented Go-ABI
assembly; it does not include the separate Firedancer-derived r43x6 reference
backend. OpenAI Codex and ChatGPT Pro, together with Anthropic Claude, assisted
with implementation, analysis, proof planning, tests, documentation, and
review; their output is not treated as correctness evidence.
