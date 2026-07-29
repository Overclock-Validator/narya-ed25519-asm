# Zen 5 cross-group batch-finalization A/B — 2026-07-29

## Scope

This record measures commit `c18be7771a98fbebd290b59cb1920d51dba9c12d`
on an AMD Ryzen 7 9700X. The candidate is the public
`narya_ed25519_verify_strict_batch` API. The control invokes the established
`narya_ed25519_verify_strict_x8` API once per group. Both routes execute the
same cold B10 equation and retain independent per-signature verdicts.

The fixture is the committed eight-lane strict fixture repeated across groups;
its message lengths deliberately vary. These numbers measure the finalizer and
dispatcher crossover. They are not a general 1232-byte throughput table and
must not replace the Go library's release benchmarks.

## Method

- Linux AMD64, GCC 15.2.0, native AVX-512 IFMA;
- one process pinned to logical CPU 2;
- 64 paired warmups of both modes;
- nine samples of 2,000 batches per width;
- sample order alternates so one mode does not always run first;
- reported values are medians in nanoseconds per signature.

## Result

| Signatures | Repeated x8 | Public batch | Change |
|---:|---:|---:|---:|
| 8 | 5780.391 | 5777.848 | -0.04% |
| 16 | 5778.745 | 5706.969 | -1.24% |
| 32 | 5766.272 | 5529.058 | -4.11% |
| 64 | 5805.396 | 5666.339 | -2.40% |

Counts through eight deliberately delegate to the old finalizer, explaining
the neutral result. Wider batches skip full `R` decompression and share one
field inversion across groups. The smaller gain at 64 than 32 is retained as
measured; the larger equation/prefix/inverse working set is a plausible cache
cost but was not established by this run.

## Correctness gates

The warning-as-error native suite and ASan/UBSan suite both passed. Coverage
includes inversion/alias boundaries, counts 1/2/4/8/9/17/32/63/64, late
failures at group edges, API output atomicity, and all 2,954 committed
RFC/CCTV/Wycheproof/boundary vectors through both public APIs.

See `commands.txt` for the exact commands, `bench_batch.c` for the harness,
the raw `*.txt` files for complete output, and `SHA256SUMS` for integrity.
