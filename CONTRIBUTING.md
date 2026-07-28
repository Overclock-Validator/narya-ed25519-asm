# Contributing

Consensus-visible arithmetic changes require more than a passing benchmark.

1. State the exact predicate or representation invariant affected.
2. Add or extend an independent scalar oracle before changing assembly.
3. Document input/output bounds, aliasing, lane movement, and CPU features.
4. Add negative tests that fail under a deliberately perturbed implementation.
5. Run native correctness on Zen 4 and Zen 5 where the path is dispatched.
6. Preserve exact commands, environments, raw output, and checksums.
7. Report complete-verifier performance; leaf-only wins remain experimental.
8. Update `NOTICE` for copied code, adapted schedules, fixtures, or datasets.
9. Run `make check-generated`; project-owned deterministic artifacts must
   reproduce byte-for-byte without network access. Externally sourced corpus
   snapshots require a pinned provenance and checksum update.
10. Run `make check-formal-hygiene` for every formal change. Project Lean may
    not contain `sorry`, `admit`, custom axioms, or other proof escapes.
11. State the exact boundary of every new theorem. A conditional theorem, a
    source-level trace theorem, and a decoded-object theorem are different
    claims and must not be presented interchangeably.
12. Keep assembly, generated traces, mutation tests, and formal audit anchors
    synchronized in one logical change. A generator accepting a changed leaf
    is not sufficient: at least one negative mutation must still be rejected.

Named range states are documentation shorthand, not proof. When an operation
leaves the immediately reusable u52 domain, record per-limb intervals for the
actual expression and prove every unsigned add/subtract is free of wrap or
underflow. Do not assume a coarse “wide” interval is closed under repeated
linear operations.

Do not weaken a CPU gate, range check, canonicality check, or fail-closed path
to recover performance. Do not promote randomized aggregate verification as
equivalent to independent per-signature verdicts.

## Reproducible formal changes

The committed `formal/lean/lake-manifest.json` is part of the reviewed input.
Ordinary proof verification uses `lake build`, never `lake update`. Run
`lake update` only in a dedicated dependency-update change, inspect every
resolved revision in the manifest, and describe why the trust-base change is
needed.

Before submitting an assembly or proof change, run:

```sh
make audit-portable
git diff --check
```

On supported native hardware also run `make check`. Preserve long native fuzz
or benchmark evidence only under `docs/reproducibility/`, with the exact source
commit, environment, commands, raw output, and checksums. Performance output
is never correctness evidence.
