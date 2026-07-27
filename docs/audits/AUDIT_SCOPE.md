# Audit scope

## Current checkpoint

The current reviewable scope is intentionally narrower than Ed25519:

- CPUID/XCR0 gate for the complete r51 feature set;
- checked r51×8 multiply/add/subtract/negate wrappers;
- SysV AVX-512 IFMA field leaves;
- C point doubling and projective-Niels addition schedules over those leaves;
- permissive compressed-point decoder with pinned scalar-Go fixtures;
- scalar differential oracles and native Zen 5 evidence.

There is no complete signature-verification API. A review of this checkpoint
must not be described as an audit of an Ed25519 verifier.

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

## Before a verifier audit

The scope must expand to SHA-512, scalar reduction, canonical-S, the exact
small-order classifier, canonical-R, table construction/selection, recoding,
double-scalar multiplication, final projective comparison, public error
semantics, corpus provenance, fuzzing, and release artifacts.
