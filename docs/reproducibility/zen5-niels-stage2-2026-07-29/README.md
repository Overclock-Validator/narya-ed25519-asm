# Zen 5 fused Niels Stage-2 A/B — 2026-07-29

This record compares standalone assembly commits
`158fc36b8db28eab475cbb108814f670c27c9bc4` and
`6c71e78b2b6c1acc099710de615c0a0561a21b6d`. The baseline already contains the register-resident decoder square,
fused doubling Stage 1+2, and typed P2 schedule. The candidate changes only the
projective- and affine-Niels additions: their raw products and linear/carry
Stage 2 move from separate field leaves into bounded assembly symbols.

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

| Statistic | Fused-doubling baseline | Fused Niels Stage 2 | Change |
| --- | ---: | ---: | ---: |
| median x8 call | 47.941 us | 46.768 us | **-2.45%** |
| median signature | 5.993 us | 5.846 us | **-2.45%** |
| mean hardware cycles | 2.715 billion | 2.687 billion | **-1.03%** |
| mean retired instructions | 8.903 billion | 8.770 billion | **-1.50%** |
| mean task clock | 490.92 ms | 486.22 ms | **-0.96%** |

All ten candidate wall-time observations were below their order-paired
baseline observations. The counter run is a separate shorter experiment and
is reported independently rather than used to override the wall-time median.

## Correctness and assurance gates

The warning-as-error native suite and ASan/UBSan suite pass at the candidate.
The field/point gate calls both new leaves directly with maximum-u52 and 256
heterogeneous random point/table inputs. It independently recomputes all four
outputs modulo `p` and asserts every exit limb is below `2^52`. Complete
variable/fixed scalar multiplication, strict verification, and all 2,954
external RFC/CCTV/Wycheproof and boundary vectors remain unchanged.

The deterministic multiplier proof ELF fixture was regenerated and the pinned
Lean project builds. This preserves the existing byte-linked multiplier
theorems; it does **not** extend them to either new Niels leaf. The new symbols
have a source-level interval certificate and native differentials. Their
assembled-byte/System V refinement remains explicitly open.

## Interpretation boundary

This is a cold, exact-x8 result for the named Zen 5 machine, commits, compiler,
fixture, and commands. It is not a singleton, warm-cache, Zen 4, or universal
performance claim.
