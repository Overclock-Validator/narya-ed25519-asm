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

Named range states are documentation shorthand, not proof. When an operation
leaves the immediately reusable u52 domain, record per-limb intervals for the
actual expression and prove every unsigned add/subtract is free of wrap or
underflow. Do not assume a coarse “wide” interval is closed under repeated
linear operations.

Do not weaken a CPU gate, range check, canonicality check, or fail-closed path
to recover performance. Do not promote randomized aggregate verification as
equivalent to independent per-signature verdicts.
