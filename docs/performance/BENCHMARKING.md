# Benchmarking rules

Correctness gates run before performance measurements. A failed or skipped
native gate invalidates every number from that binary.

## Required labels

Every reported result states:

- source commit and dirty status;
- CPU model, microcode where available, OS, compiler, and flags;
- batch width and active-lane mask;
- message size and verification profile;
- cold, decoded-key, or precomputed-key state;
- public API or private core seam;
- time unit and whether the number is per call, group, or signature.

## Stable measurements

Pin one physical core and use a performance governor for primitive and
single-core results. Record at least ten multi-second samples and retain raw
output. Multi-core runs state worker count and distinguish aggregate
signatures/second from single-core signatures/second.

Assembly-only microbenchmarks are diagnostic. A change is promoted on complete
verification time, predicate equivalence, allocation/stack behavior, and code
size—not on a leaf result alone.

`build/bench_verify_batch` accepts a final mode of `public`, `padded`, or
`both`. `public` measures the real dispatcher. `padded` forces the legacy
signature-x8 strategy for counts one and two and is diagnostic only. `both`
alternates the two in one binary to produce a same-run A/B. The current packed
small-batch commands and raw samples are in the
[2026-07-29 record](../reproducibility/zen5-packed-small-2026-07-29/README.md).

## Hardware policy

Zen 4 and Zen 5 may select different schedules. A policy decision requires a
native measurement on the relevant family; SDE and static instruction models
provide correctness or hypotheses, not dispatch performance evidence.
