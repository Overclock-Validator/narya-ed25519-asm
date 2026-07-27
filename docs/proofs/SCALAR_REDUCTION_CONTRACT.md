# Scalar-reduction contract

## Claim

`narya_scalar_reduce_x8` maps each active 512-bit little-endian input to the
unique 32-byte little-endian representative in `[0,l)`, where

```text
l = 2^252 + 27742317777372353535851937790883648493.
```

Inactive outputs are zero and lanes are independent.

## Reduction identity

The native leaf stores 24 signed radix-`2^21` limbs in ZMM registers. For a
coefficient at position `i >= 12`, it uses the exact congruence

```text
2^252 =
  666643 + 470296*2^21 + 654183*2^42 - 997805*2^63
  + 136657*2^84 - 683901*2^105                    (mod l).
```

The schedule folds limbs 23 through 18, performs centered signed carries,
folds limbs 17 through 12, then performs two final fold/carry passes. The last
pass leaves twelve nonnegative limbs which the wrapper packs into 252 bits.

## Machine obligations

The source leaf uses `VPMULLQ`, signed `VPSRAQ`, additions, and subtractions.
Its proof obligations are:

1. every mathematical intermediate fits signed 64-bit, so low-product
   truncation is exact;
2. arithmetic right shift implements floor division by `2^21` for negative
   as well as positive limbs;
3. every fold preserves the input modulo `l`;
4. final limbs pack to a value below `l`;
5. no instruction mixes lanes;
6. the wrapper parses all input before publishing output, establishing exact
   input/output alias safety and error atomicity.

Tests exercise edge values, all 256 active masks, exact aliasing, and 10,000
random x8 inputs. Their oracle performs 512 shift-and-conditional-subtract
steps against the literal order and shares none of the native fold constants,
radix limbs, carry schedule, or packing expressions.

## Formalization target

This schedule is the second recommended machine-checked target after the r51
field multiply. A useful Lean theorem should prove the six obligations above
over arbitrary eight-tuples, followed by a bitvector refinement from the
assembly instructions to the signed-limb model. See
[`FORMALIZATION_BACKLOG.md`](FORMALIZATION_BACKLOG.md).
