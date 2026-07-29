# Zen 5 decoder square-chain A/B — 2026-07-28

This record compares standalone assembly baseline
`571f224057b11faa1f0fd968d6d282d515a4a7bf` with the dirty candidate diff that
adds `narya_r51x8_repeated_square_ifma` and uses it in `pow22523`.

## Scope

- public `narya_ed25519_verify_strict_x8` API;
- eight valid, cold public keys per call with caller-owned workspace reuse;
- active mask `0xff`;
- message lengths 0, 1, 17, 64, 200, 511, 1232, and 4096 bytes;
- one process-shared immutable fixed-base comb;
- one pinned logical CPU, performance governor;
- ten alternating baseline/candidate samples, 40,000 x8 calls per sample;
- 256 untimed warm-up calls in each benchmark process.

The warning-as-error native suite and ASan/UBSan native suite passed before
the result was recorded. That includes exact square-chain comparison against
the independent `__uint128_t` oracle for counts through 252, exact aliasing,
256 permissive decoder vectors, independent strict signatures, and 2,954
external RFC/CCTV/Wycheproof and boundary vectors.

The canonical Linux proof ELF was regenerated after adding the adjacent
symbol. Its whole-file provenance hash changed, while the multiplier symbol's
800 bytes and SHA-256 remained exactly unchanged; `make
check-r51-object-bytes` passed.

## Result

| Statistic | General-multiply chain | Register-resident square chain | Change |
| --- | ---: | ---: | ---: |
| mean x8 call | 53.142 us | 50.824 us | **-4.36%** |
| mean signature | 6.643 us | 6.353 us | **-4.36%** |
| median x8 call | 52.790 us | 50.883 us | **-3.61%** |

All ten candidate observations were below all ten baseline observations. The
result is a complete-verifier measurement, not an isolated leaf estimate.
The new symbol is 790 bytes; alignment raises `r51x8_ifma.o` text from 1,569
to 2,369 bytes.

## Interpretation boundary

This is evidence for this Zen 5 machine and exact cold-key workload. It is not
a Zen 4 dispatch result or a universal performance claim. Native differential
testing and the source-level bound in `R51_FIELD_CONTRACT.md` do not close the
new leaf's machine-checked trace or assembled-byte refinement; that obligation
remains explicit in `FORMALIZATION_BACKLOG.md`.
