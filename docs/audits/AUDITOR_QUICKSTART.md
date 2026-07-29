# Auditor quickstart

This document gives a shortest reproducible path through the current evidence.
It does not turn project-owned checks into an independent audit, and it does
not expand any theorem beyond the boundary stated in the
[formal evidence index](../proofs/FORMAL_EVIDENCE_INDEX.md).

## 1. Establish the reviewed input

Record the commit and require a clean tracked tree:

```sh
git rev-parse HEAD
git status --short
```

Review changes to all of these as trust-base changes, not routine generated
noise:

- `formal/lean/lean-toolchain`;
- `formal/lean/lake-manifest.json`;
- `.github/workflows/` action revisions;
- generators and source parsers under `tools/`; and
- the canonical proof-link rules in `Makefile`.

The normal verification procedure never runs `lake update`. The committed
manifest fixes the complete Lean dependency graph.

## 2. Run the portable deterministic gate

On a host with Python 3, Clang, an ELF linker, and the pinned Lean toolchain:

```sh
make audit-portable
```

This gate:

1. parses every assembly leaf for an x86-64 ELF target;
2. regenerates and compares every project-owned deterministic artifact;
3. runs mutation tests against the r51, transpose, and scalar-reduction
   source extractors;
4. validates the scalar-reduction bounds and SHA-512 schedule certificate;
5. rejects Lean proof escapes and missing stable audit anchors; and
6. builds the pinned Lean project.

On Linux, additionally link and check the canonical multiplier proof ELF:

```sh
make CLANG=clang LD=ld check-r51-object-bytes
```

That ELF is a deterministic proof fixture. It is not a claim that arbitrary
downstream linkers emit identical deployment bytes.

## 3. Run portable native-code tests

The ordinary suite selects portable reference paths when IFMA is unavailable:

```sh
make clean
make CC=clang \
  CFLAGS='-O2 -g -std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror' \
  test
```

Reviewers should perturb at least one range constant, transpose immediate, and
strict-predicate boundary in a disposable branch and confirm that the relevant
negative test fails. Passing an unmodified project-owned corpus is weaker
evidence than demonstrating that its gates detect the targeted defect class.

## 4. Run the real hardware gate

Only a Linux AMD64 host with the required AVX-512 IFMA and OS state can execute
the promoted assembly. On such a machine:

```sh
make check
make CC=clang test-sanitize
make CLANG=clang fuzz-build
./build/fuzz_verify_strict_x8 -runs=50000 tests/fuzz/corpus/verify_strict_x8
```

`NARYA_REQUIRE_IFMA=1` is set by the native targets so a missing CPU/OS feature
cannot silently turn this into another portable run. Emulation and assembly
parsing are useful regression evidence, never native correctness or performance
evidence.

## 5. Review in dependency order

The recommended human-review order is:

1. [strict predicate](../architecture/STRICT_PREDICATE.md), including original
   hash bytes, small-order policy, and canonical-R equivalence;
2. [ABI and layouts](../architecture/ABI.md), dispatch, feature gating, aliasing,
   and lane-to-result mapping;
3. [r51 field contract](../proofs/R51_FIELD_CONTRACT.md), source extractors,
   restricted decoder, and exact theorem statements;
4. decoder and the [point-doubling schedule](../architecture/POINT_DOUBLING.md),
   including its separate Stage-2 proof boundary;
5. scalar reduction and recoding;
6. SHA-512 message segmentation and compression;
7. variable-base scalar multiplication, the merged asymmetric B10 schedule,
   and the independent radix-256 fixed-base oracle; and
8. complete-verifier differentials, faults, masks, and inactive lanes.

The [audit scope](AUDIT_SCOPE.md) lists the high-priority questions. The
[formal evidence index](../proofs/FORMAL_EVIDENCE_INDEX.md) names the strongest
machine-checked entry point for each formalized claim.

## 6. Current formal stopping points

The strongest byte-linked proof, `run_r51_multiplier_refines`, covers the
complete decoded r51 multiplier leaf: preparation, arithmetic, stores,
semantic independence from arbitrary ZMM28--31 entry values, source/output
aliasing, preserved disjoint return word, `VZEROUPPER`, and `RET`. It stops
before wrapper/dispatch refinement, physical CPU correctness, concurrent
memory mutation, and identity with a downstream deployment binary.

The scalar reducer now has a position-pinned 389-step source certificate and a
machine-checked canonical-tail theorem. Its C parser/packer and 434-instruction
assembled-byte refinement remain open. The transpose, SHA-512 leaf, decoder,
point formulas, and complete verifier likewise have narrower source
certificates, algebraic lemmas, tests, or conditional specifications as
documented. Do not infer byte-linked or whole-verifier correctness from those
smaller claims.

## 7. Reporting

Follow the root `SECURITY.md`. Potential consensus divergence, unsafe memory
behavior, or a crafted arithmetic mismatch should be reported privately with
the exact commit, CPU, compiler, reproducer, expected result, and observed
result. Do not publish an exploit or unpublished divergence vector before a
private reporting channel is established.
