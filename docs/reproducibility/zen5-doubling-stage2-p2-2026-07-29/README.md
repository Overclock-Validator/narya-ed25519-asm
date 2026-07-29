# Zen 5 fused doubling Stage-2/P2 A/B — 2026-07-29

This record compares standalone assembly commit
`1b017662881e09c93f7fe387ece65df841124add` with
`217323b6238b9c756bc61f5d9c8860263e4dd386`. The candidate fuses four raw doubling products with the direct-XY
linear Stage-2 and uses a distinct P2 `(X,Y,Z)` state for intermediate
doublings.

## Scope

- public `narya_ed25519_verify_strict_x8` API;
- eight valid, cold public keys per call with caller-owned workspace reuse;
- active mask `0xff`;
- heterogeneous lane messages of 0, 1, 17, 64, 200, 511, 1232, and 4096
  bytes from the pinned strict fixture;
- one pinned logical CPU under the performance governor;
- ten order-balanced baseline/candidate samples, 20,000 x8 calls per sample;
- 256 untimed warm-up calls in each benchmark process; and
- five `perf stat` repetitions of 10,000 calls for cycles, instructions, and
  task clock.

## Complete-verifier result

| Statistic | Decoder-square baseline | Fused Stage-2 + P2 | Change |
| --- | ---: | ---: | ---: |
| median x8 call | 50.693 us | 47.767 us | **-5.77%** |
| median signature | 6.337 us | 5.971 us | **-5.77%** |
| mean hardware cycles | 2.873 billion | 2.722 billion | **-5.27%** |
| mean retired instructions | 9.647 billion | 8.903 billion | **-7.71%** |
| mean task clock | 518.98 ms | 492.51 ms | **-5.10%** |

All ten candidate wall-time observations were below all ten baseline
observations.

An additional counter run compared the fused schedule with and without P2
intermediates. P2 reduced retired instructions by 3.10%, cycles by 0.57%, and
task clock by 0.53%. This is why the typed omission is promoted only together
with Stage-2 fusion; the earlier unfused P2-only timing was inconclusive.

## Correctness and assurance gates

The warning-as-error native suite and ASan/UBSan suite pass at the candidate.
The field/point gate adds an independent check of all four Stage-2 outputs for
maximum-u52 and heterogeneous random inputs, asserts every exit limb is u52,
and exercises P3-to-P2, exact in-place P2-to-P2, and P2-to-P3 chains. The
complete scalar-multiplication fixtures, strict signatures, and 2,954 external
RFC/CCTV/Wycheproof and boundary vectors remain unchanged.

The deterministic Linux proof ELF was regenerated and
`make check-r51-object-bytes` passes. That check continues to cover the
ordinary multiplier symbol. The new raw-product/Stage-2 leaf and P2 point
composition have source-level certificates and native differentials but do
not yet have byte-linked Lean refinement theorems.

The pinned Lean project builds after refreshing the deterministic multiplier
object fixture; this preserves all existing theorems without expanding them to
the new Stage-2 symbol.

## Interpretation boundary

This is a cold x8 result for the exact Zen 5 machine, source commits, compiler,
fixture, and commands in this directory. It is not a singleton, warm-cache,
Zen 4, or universal performance claim.
