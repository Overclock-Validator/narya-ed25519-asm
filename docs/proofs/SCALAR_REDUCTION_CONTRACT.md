# Scalar-reduction contract

## Status

This document specifies `narya_scalar_reduce_x8`. The source-level signed
interval certificate is executable and checked in CI. It pins every macro
argument and the rounded-carry broadcast, proves the real source schedule
cannot overflow signed 64-bit intermediates under the stated parser bounds,
and establishes the checkpoint interval used by the machine-checked
canonical-tail theorem. The reconstructed source-level result is therefore in
`[0,l)` under those initial bounds. It does **not** yet prove the C
parser/packer refinement or assembled-binary instruction refinement. Native
differential and boundary tests cover those wider claims only over finite
corpora.

## Claim

For each active lane, `narya_scalar_reduce_x8` interprets the 64-byte input as
an unsigned 512-bit little-endian integer `X` and writes the unique 32-byte
little-endian integer `Y` satisfying

```text
0 <= Y < l
Y = X (mod l)
l = 2^252 + 27742317777372353535851937790883648493.
```

Canonical outputs may use bit 252; bits 253 through 255 are zero. In
particular, `l-1` has bit 252 set and must not be truncated to 252 bits.
Inactive output rows are zero. Logical lanes are independent.

The top-level arithmetic theorem is:

```text
for every X in [0, 2^512), ReduceSchedule(X) = X mod l,
with ReduceSchedule(X) in [0, l).
```

## Radix parsing

Let `B = 2^21`. The C wrapper constructs positional coefficients
`s[0]..s[23]` such that

```text
X = sum(s[i] * B^i, i=0..23).
```

The exact initial bounds are

```text
0 <= s[i] < B       for 0 <= i <= 22
0 <= s[23] < 2^29.
```

The wider top coefficient is load-bearing: 23 ordinary 21-bit positions
cover only 483 bits. A parsing proof must refine the byte loads and shifts in
`load_radix21_x8`; it must not infer these bounds merely from the intended
layout.

## Reduction identity

Let

```text
c = l - 2^252.
```

The constants obey the exact integer identity

```text
666643 + 470296*B + 654183*B^2 - 997805*B^3
       + 136657*B^4 - 683901*B^5 = -c.
```

Therefore

```text
B^12 = 666643 + 470296*B + 654183*B^2 - 997805*B^3
       + 136657*B^4 - 683901*B^5                    (mod l).
```

For a coefficient at position `i >= 12`, `FOLD` applies this congruence after
multiplication by `B^(i-12)`, then clears the consumed high coefficient. The
schedule folds coefficients 23 through 18, performs centered carries, folds
17 through 12, and performs two final fold/carry passes.

`NaryaFormal.ScalarReduction.fold_polynomial_exact` machine-checks this exact
identity, and `radix12_fold_mod_order` proves the resulting congruence modulo
`l`.

## Carry semantics

The native schedule uses two distinct transformations.

A centered carry computes

```text
q = floor((x + 2^20) / B)
r = x - q*B,
```

and establishes

```text
-2^20 <= r < 2^20.
```

An ordinary carry computes

```text
q = floor(x / B)
r = x - q*B,
```

and establishes

```text
0 <= r < B.
```

In both cases the adjacent-coefficient update

```text
(x_i, x_(i+1)) -> (x_i - q*B, x_(i+1) + q)
```

preserves the represented integer exactly. `NaryaFormal.ScalarReduction`
proves both quotient/residual decompositions, both residual ranges, and the
generic adjacent-coefficient preservation theorem. The source certificate
separately proves that adding `2^20` and reconstructing `q*B` stay within
signed int64 for every occurrence in the real schedule.

## Canonical range and packing

After the final schedule, define

```text
Y = sum(s[i] * B^i, i=0..11).
```

Canonicality is the independent theorem

```text
0 <= Y < l.
```

It must not be inferred merely from final limb widths. The checked proof uses
the state immediately after the first final fold: its weighted interval is
strictly inside `(-B^12,B^12)`. The first ordinary carry can therefore produce
only top coefficient `-1` or `0`; the second fold is exactly a conditional
addition of `l`, yielding `[0,l)`. This argument is machine checked in
`NaryaFormal.ScalarReductionCanonicalTail`.

Assuming
`0 <= s[i] < B` for `i < 11`, the top coefficient may satisfy
`0 <= s[11] <= B`; when `s[11] = B`, the lower reconstruction must be below
`c`. This is how values in `[2^252,l)`, including `l-1`, are represented.

The separate packing theorem is

```text
LE256(output) = Y.
```

Parsing, modular preservation, canonical range, and exact packing together
establish that the output is `X mod l`.

## Source-level machine-range certificate

The assembly leaf uses `VPMULLQ`, signed `VPSRAQ`, `VPADDQ`, `VPSUBQ`, and
fixed shifts. [`check_scalar_reduce_bounds.py`](../../tools/check_scalar_reduce_bounds.py)
parses the actual macros, constants, limb loads/stores, and macro-call order.
It compares the complete normalized source transcript against a pinned list,
so fold positions, carry adjacency, and the rounded-carry constant load are
semantic inputs rather than unchecked assumptions.
It exposes bounds after every arithmetic instruction and proves:

1. for every `VPMULLQ`, the intended signed product is in
   `[-2^63,2^63-1]`, so its low 64-bit two's-complement result is exact;
2. every partial addition and subtraction also remains in that interval;
3. adding the centered-carry bias and reconstructing `q*B` cannot overflow;
4. each arithmetic right shift implements the specified floor division;
5. every position-pinned fold preserves the represented value modulo `l`;
6. every carry moves its quotient to the adjacent radix position; and
7. the first-final-fold weighted interval lies inside
   `(-2^252,2^252)`, which feeds the canonical-tail theorem.

It is insufficient to bound only the final node of a fold or carry: every
partial multiplication and accumulation is certified. The current source has
389 checked intermediates. The largest absolute bound is
`537126723016406` (49 bits), at the subtraction of `683901*zmm21` from
`zmm14`, leaving more than fourteen signed bits of headroom.

Run the concise gate with:

```sh
make check-scalar-bounds
```

or emit every interval and transfer rule as JSON with:

```sh
python3 tools/check_scalar_reduce_bounds.py --json
```

The final independent intervals are `0..2^21-1` for limbs 0 through 10,
`-1..2^21` for limb 11, and zero at limb 12. Those final intervals still do
not imply canonicality alone. The earlier one-window checkpoint plus exact
carry/fold relations now establish the reconstructed value in `[0,l)`.
Exact C packing, including bit 252, remains open.

`test_scalar_reduce_bounds_positional_mutations.py` proves the checker has
teeth against a swapped fold target, a nonadjacent carry, and a deleted
rounded-carry broadcast. See the
[2026-07-28 review follow-up](../audits/SCALAR_REDUCTION_REVIEW_2026-07-28.md).

## Remaining machine obligations

The source certificate and canonical-tail theorem are linked by checked
numeric hypotheses, not by one Lean theorem over a decoded program. The source
certificate does not decode emitted instruction bytes. A full
instruction-refinement proof must still show that the assembled opcodes and
register map implement the certified macro trace. The C boundary also needs
proof that parsing establishes the certificate's initial bounds and packing
preserves the proved canonical integer.

## Lane and wrapper obligations

The arithmetic leaf is lane-separable: each ZMM lane computes the same scalar
schedule and no leaf instruction mixes lanes. This is distinct from the C
wrapper theorem. The wrapper must prove that:

1. its byte-to-radix parsing preserves each logical lane;
2. inactive lanes are zeroed before entering the leaf and before publication;
3. all argument and CPU checks occur before the first output store;
4. every input byte needed by every active lane is materialized before the
   first output store;
5. after publication begins, no error is possible;
6. on error, the entire destination remains unchanged.

The current wrapper materializes all 512 input bytes into private limb state
and builds a private result before one final `memcpy`. Its intended ABI is
therefore safe for arbitrary overlap between the 256-byte output range and
the 512-byte input range, not only exact start-address aliasing. The memory
proof remains separate from the scalar arithmetic proof.

## Executable evidence

`tests/test_scalar_reduce.c` uses a bit-at-a-time modulo-`l` oracle that
shares none of the leaf's fold constants, radix limbs, carries, or packing
expressions. Deterministic coverage includes:

- `0`, `1`, `2^252-1`, `2^252`, `l-2`, `l-1`, `l`, `l+1`, `2l-1`, `2l`, and
  `2^512-1`;
- isolated maximum radix coefficients, including `s[23]=2^29-1`;
- eight distinct adversarial lanes under all 256 active masks;
- inactive-output zeroing, arbitrary source/output overlap, and error
  atomicity;
- 10,000 random x8 inputs.

The committed adversarial JSON is regenerated by
`tools/generate_scalar_reduction_vectors.py` using Python arbitrary-precision
reduction rather than the assembly schedule. It includes 31 scalar cases, the
two exact widest-bound witnesses, and an eight-lane mixed bundle.

The `l-1` regression additionally asserts that output bit 252 survives.
These tests are evidence, not a substitute for the formal range and memory
proofs.

## Formalization split

The recommended theorem boundaries are:

```text
parse_radix21_correct
fold_identity_correct
centered_carry_exact
ordinary_carry_exact
schedule_congruent_mod_l
schedule_signed_bounds
final_value_canonical
pack32_exact
scalar_reduce_correct
leaf_bitvector_refinement
x8_lane_mapping
active_mask_semantics
wrapper_alias_and_atomicity
```

The arithmetic theorem should be proved before the bit-vector refinement.
The wrapper memory theorem remains separate because it reasons about pointer
ranges, loads, stores, and error paths rather than modular arithmetic. See
[`FORMALIZATION_BACKLOG.md`](FORMALIZATION_BACKLOG.md).
