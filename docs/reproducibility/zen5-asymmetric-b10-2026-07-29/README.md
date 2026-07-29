# Zen 5 merged asymmetric B10 A/B — 2026-07-29

This record compares standalone assembly commits
`344afa3d180f24cee3dfe15b661362b56086358c` and
`fe951d35d59fb8299d1da5a7ae5a4ed27b8959f7`. The baseline already contains the register-resident decoder square,
fused doubling/P2 schedule, and fused projective/affine-Niels Stage 2. The
candidate changes only complete double-scalar evaluation: a width-10 immutable
generator table is injected into the variable term's existing radix-32 chain.

## Scope

- public `narya_ed25519_verify_strict_x8` API;
- eight valid, cold public keys per call with caller-owned workspace reuse;
- active mask `0xff`;
- heterogeneous lane messages of 0, 1, 17, 64, 200, 511, 1232, and 4096
  bytes from the pinned strict fixture;
- one pinned logical CPU under the performance governor;
- six order-balanced baseline/candidate samples, 100,000 x8 calls per sample;
- 256 untimed warm-up calls in each benchmark process; and
- five `perf stat` repetitions of 10,000 calls for cycles, instructions, and
  task clock.

## Complete-verifier result

| Statistic | Separate radix-256 + variable terms | Merged B10 schedule | Change |
| --- | ---: | ---: | ---: |
| median x8 call | 47.265 us | 45.376 us | **-3.99%** |
| median signature | 5.908 us | 5.672 us | **-3.99%** |
| mean hardware cycles | 2.677 billion | 2.535 billion | **-5.31%** |
| mean retired instructions | 8.770 billion | 8.577 billion | **-2.20%** |
| mean task clock | 484.72 ms | 460.23 ms | **-5.05%** |

The longer wall-time samples supersede a noisier short run that showed a
larger median improvement. The counter run is a separate shorter experiment;
it is reported independently rather than used to replace the wall-time result.

## Correctness and assurance gates

The warning-as-error native suite and ASan/UBSan suite pass at the candidate.
The merged evaluator is compared projectively against a deliberately separate
construction using the independent radix-256 comb and variable-base evaluator
across 32 heterogeneous x8 groups. The native gate also sweeps all 256 active
masks and checks lane-local rejection of noncanonical generator and variable
scalars. Complete strict verification passes all 2,954 external
RFC/CCTV/Wycheproof and boundary vectors.

`tools/check_generated.py` reproduces both immutable fixed-base payloads. The
B10 payload has SHA-256
`82c05fbe7a74131355010cbd3605fae76630f3df0e991917a0ba11697bdb9d7d`.
The abstract group recurrence is documented in
`docs/architecture/ASYMMETRIC_FIXED_B10.md`; the C schedule, scalar recoders,
and embedded table do not yet have a byte-linked Lean refinement.

## Interpretation boundary

This is a cold, exact-x8 result for the named Zen 5 machine, commits, compiler,
fixture, and commands. It is not a singleton, warm-cache, Zen 4, or universal
performance claim. The immutable generator table is process-shared constant
data; no public-key state is retained.
