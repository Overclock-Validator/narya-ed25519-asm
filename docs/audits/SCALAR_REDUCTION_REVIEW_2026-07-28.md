# Scalar-reduction review follow-up — 2026-07-28

## Scope and disposition

An external proof-oriented review examined the signed radix-`2^21` scalar
reducer at commit `7159874474dce2e3e9aabad3478f8e8d36ce3de2`.
It found no arithmetic counterexample in the assembly schedule. It independently
reproduced all 389 source-certificate intervals and the 49-bit maximum absolute
intermediate.

The review did find a real assurance defect in the project-owned checker: it
propagated bounds through whichever register arguments appeared in a parsed
`FOLD` or carry call, but did not prove that those registers were the required
radix positions. It also did not require the rounded-carry constant broadcast.
This meant an arithmetic-breaking edit could remain range-safe and pass a
checker that reported modular preservation.

The commit containing this document resolves that defect and adds the
canonical-tail proof described below. It does **not** close the C parser,
packer, emitted-opcode, wrapper, or physical-CPU boundaries.

## Source-certificate repair

[`check_scalar_reduce_bounds.py`](../../tools/check_scalar_reduce_bounds.py)
now pins the normalized 60-macro transcript, including:

- all 14 `FOLD` calls and their seven register arguments;
- all 23 centered carries and 23 ordinary carries with adjacent targets; and
- the single `2^20` rounded-carry broadcast in its exact schedule position.

The negative gate
[`test_scalar_reduce_bounds_positional_mutations.py`](../../tools/test_scalar_reduce_bounds_positional_mutations.py)
requires rejection of three range-safe semantic mutations:

1. swapping two equally bounded low targets of the first fold;
2. redirecting a centered carry to a nonadjacent radix position; and
3. deleting the rounded-carry constant broadcast.

The mutation test is part of `make check-source` and therefore
`make audit-portable`.

## Exact algebraic schedule

Let

```text
B = 2^21
V(s) = sum_i s_i B^i
L = 2^252 + 27742317777372353535851937790883648493
F = 666643 + 470296 B + 654183 B^2 - 997805 B^3
    + 136657 B^4 - 683901 B^5
```

The machine-checked identity `F = B^12-L` implies that a complete fold of a
coefficient `h` at position `i >= 12` has exact integer effect

```text
V_after = V_before - h L B^(i-12).
```

Every complete adjacent centered or ordinary carry preserves `V` exactly.
The pinned source transcript consists of 14 folds, 23 centered carries, and
23 ordinary carries: 60 macros and 389 arithmetic instructions.

## Signed bounds

The independently reproduced maximum interval is

```text
[-537126723016406, 286592461358]
```

at the subtraction of `683901*zmm21` from `zmm14`. The maximum absolute
endpoint is below `2^49`, leaving more than fourteen signed headroom bits.
The complete 389-row trace is reproducible with:

```sh
python3 tools/check_scalar_reduce_bounds.py --json
```

Two concrete digests attain the negative and positive endpoints of that
update. They are generated in
[`narya_scalar_reduction_adversarial_v1.json`](../../tests/vectors/narya_scalar_reduction_adversarial_v1.json)
and exercised as distinct lanes under all 256 active masks by the native C
test.

The reported per-operation intervals are sound inclusive abstract bounds.
They are not all claimed to be globally attainable extrema over the original
24 input digits; the analysis intentionally drops correlations at carry
residuals. No-overflow does not require the stronger global-tightness claim.

## Canonical-tail proof

Immediately after the first final fold and before the first ordinary carry
pass, the source certificate now records the exact independent limb intervals
and verifies that their weighted hull lies strictly inside

```text
(-B^12, B^12) = (-2^252, 2^252).
```

The first ordinary carry chain preserves the represented value and decomposes
it as `V = R + q B^12`, with `0 <= R < B^12`. The strict one-window bound
forces `q` to be `-1` or `0`. Because `F=B^12-L`, the second fold either leaves
`R` unchanged or adds `L` to the negative representative. Both cases land in
`[0,L)`, and the final carry chain preserves that canonical integer.

[`ScalarReductionCanonicalTail.lean`](../../formal/lean/NaryaFormal/ScalarReductionCanonicalTail.lean)
machine-checks:

- arbitrary-position exact fold delta and congruence;
- the weighted first-final-fold interval theorem;
- the one-window top-carry case split;
- canonicality of the second fold; and
- the legal top-limb/bit-252 condition.

These theorems contain no proof escapes or custom axioms and build under the
pinned Lean 4.19.0/mathlib toolchain. Their hypotheses are tied to the assembly
source by an executable Python certificate, not yet by a byte-decoded Lean
refinement theorem. That distinction remains part of the trust boundary.

## Remaining obligations

Still open:

1. exact 64-byte C parser refinement into the 24 radix limbs;
2. exact canonical-limb-to-32-byte packer refinement, including bit 252;
3. signed x86 `BitVec` semantics and byte-linked refinement for the 434
   assembled instructions;
4. wrapper active-mask, arbitrary-overlap, and error-atomicity proofs; and
5. identification with a downstream deployment binary and physical-CPU
   conformance.

The native oracle, deterministic vectors, active-mask sweep, alias tests, and
random differential are finite evidence for those boundaries, not universal
proofs.
