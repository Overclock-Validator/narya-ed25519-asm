# Verification refinement spine

Formal components compose only when they share explicit abstraction
functions and theorem shapes. This document fixes that shape before the
remaining decoder, group, scalar-reduction, and wrapper proofs are added.

## Commuting-square rule

Every implementation layer must expose an abstraction into its mathematical
domain and prove a commuting square. For example, the field layer uses the
radix-51 value modulo `p`:

```text
machine limbs --native multiply--> machine limbs
      |                                |
      | abstract mod p                 | abstract mod p
      v                                v
      F_p --------field multiply-----> F_p
```

Equivalent requirements apply to scalar parsing/reduction, permissive point
decoding, point operations, SHA-512, final equality, and verdict packing.
The abstraction function is part of the interface between proofs; equivalent
but independently invented representations are not accepted implicitly.

[`VerificationSpine.lean`](../../formal/lean/NaryaFormal/VerificationSpine.lean)
states the capstone theorem now, with every unfinished square represented by a
typed hypothesis. This makes the formal hypothesis list the live audit scope.
As individual hypotheses are discharged, the capstone statement remains
unchanged.

## Full-group rule

The point abstraction lands in the full Edwards group, including its
eight-torsion component. Scalar action on points is integer action (`ℤ`-smul),
not action by `ZMod L`.

This is load-bearing. `DalekStrict` rejects pure small-order public keys and R
points but accepts mixed-order points. Replacing an integer scalar by its
residue modulo the prime subgroup order can therefore change the torsion
component. A scalar-multiplication theorem stated only in the prime-order
quotient is insufficient even if it is correct for ordinary prime-subgroup
test vectors.

Scalar reduction still lands in `[0,L)` as an integer. The resulting integer
acts on the full decoded point; the point is never silently projected into
the prime-order subgroup.

## Scalar proof plus lane projection

Protocol and group theorems are proved once for a scalar input. Each SIMD
kernel then owes one lane-projection/noninterference lemma showing that native
lane `i` equals scalar execution on input `i`.

The top x8 theorem has this form:

```text
native_verdict(inputs)[i] = true
    iff
DalekStrict(inputs[i])
```

The only SIMD-specific premise is `hLane`. The transpose certificate is one
part of eventually discharging that premise; it is not by itself a proof of
the complete lane computation.

## Predicate fixed by the capstone

The pure predicate in the Lean spine states:

1. the little-endian scalar value is below `L`;
2. A and R decode through the permissive decoder;
3. neither decoded point satisfies `[8]P = O`;
4. re-encoding decoded R reproduces the original R bytes; and
5. `[S]B - [k]A = R` in the full group, where
   `k = reduce(SHA512(original_R || original_A || message))`.

The R round trip is the mathematical restatement of the terminal compressed
byte comparison. The original R and A encodings—not canonicalized
re-encodings—flow into the challenge hash.

The theorem is an `iff`. A verifier that rejects every input cannot satisfy
it merely by being sound.

## Current hypothesis ledger

`verifyStrictX8_correct` currently requires:

- scalar byte parsing and the `S < L` boolean;
- permissive A/R decoder equivalence;
- pure-small-order classifier equivalence;
- canonical-R/round-trip equivalence;
- SHA-512 over the original byte segments;
- digest reduction modulo `L`;
- the full-group verification equation; and
- native x8 lane projection and verdict indexing.

Existing field, transpose, SHA schedule, and scalar-reduction work supports
these obligations but does not automatically discharge them. In particular,
source-level arithmetic proofs do not establish emitted-object behavior or
the C wrapper's pointer, length, dispatch, and error semantics.

## Evidence pairing

Each hypothesis should have both a universal proof target and an executable
differential target. The latter does not replace the former, but it gives the
same property a hardware regression gate while refinement work continues.

Examples:

- `hDecode`: permissive aliases, invalid square roots, sign-of-zero cases;
- `hSmallOrder`: all 14 encodings and neighboring byte mutations;
- `hReduce`: `L-1`, `L`, `2L`, `2^512-1`, carry maxima, all lane masks;
- `hHash`: segmented unequal-length messages and every padding boundary;
- `hLane`: unique lane tags, every active mask, and independent failures;
- `hEquation`: mixed-order points and non-unit projective Z values.

## What this does not prove

The capstone is a conditional composition theorem. It does not assert that
the current object code satisfies its hypotheses. Emitted-opcode refinement,
complete point-formula refinement, decoder refinement, wrapper refinement,
and the final native lane theorem remain open. Those boundaries must remain
visible in audit and release documentation.

Warm-key cache and warm-comb policy are intentionally outside this spine. The
target here is the cold verifier's common arithmetic and exact acceptance
predicate.
