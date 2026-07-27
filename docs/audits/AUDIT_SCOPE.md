# Audit scope

## Current checkpoint

The current reviewable scope contains a complete ABI-zero strict verifier:

- CPUID/XCR0 gate for the complete r51 feature set;
- checked r51×8 multiply/add/subtract/negate wrappers;
- SysV AVX-512 IFMA field leaves;
- C point doubling and projective-Niels addition schedules over those leaves;
- permissive compressed-point decoder with pinned scalar-Go fixtures;
- SysV x8 rolling-register SHA-512 compression with scalar and FIPS oracles;
- canonical scalar reduction and exact signed radix-32 recoding;
- pre-signed projective-Niels table construction and assembly transpose;
- variable-base scalar multiplication and complete `[S]B-[k]A` evaluation;
- canonical-S, exact small-order A/R, canonical-R, projective equality, and
  independent lane verdicts;
- scalar differential oracles and native Zen 5 evidence.

The fixed-base term deliberately uses the variable-base engine in this
checkpoint. That is slower but predicate-equivalent. Performance claims must
wait for the radix-256 fixed-base replacement and dedicated benchmarks.

## High-priority review questions

1. Are every IFMA source and accumulator bound sufficient and correctly tied
   to its call site?
2. Is `VPMULLQ` by 19 exact under the proved pre-fold bound?
3. Does every alias-safe leaf load all necessary data before any store?
4. Is the CPUID/XCR0 gate at least as strong as every instruction reachable
   after it?
5. Can any instruction, mask, or future transpose mix independent verdict
   lanes or mis-map a lane back to its caller index?
6. Does the decoder exactly implement the pinned permissive byte semantics,
   especially `y >= p` and `x = 0` with sign bit one?
7. Is explicit canonical-R plus decoded projective equality exactly equivalent
   to dalek 2.x's terminal compressed-byte comparison?
8. Does digit-level negation preserve exact signed-integer semantics for
   mixed-order public keys?

## Before release

The scope must expand to CCTV and Wycheproof ingestion, committed fuzz seeds,
long native fuzz soaks, independent regeneration of all byte classifiers,
fixed-base-comb evidence, ABI-version review, fault containment, benchmark
artifacts, and at least one independent implementation audit.
