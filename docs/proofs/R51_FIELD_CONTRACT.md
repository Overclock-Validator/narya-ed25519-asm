# r51×8 field contract

This note states the obligations enforced by `narya_r51x8_mul_ifma`.

The representation algebra is machine-checked in
[`Radix51.lean`](../../formal/lean/NaryaFormal/Radix51.lean). The exact scalar
trace corresponding to `narya_r51x8_mul_ifma` is checked in
[`AssemblyTrace.lean`](../../formal/lean/NaryaFormal/AssemblyTrace.lean).
Together they prove the 52-bit IFMA split identity, the assembly's row-major
25-product grouping, every accumulator prefix bound, `COMBINE_HIGH`, the
`2^255 = 19 (mod p)` fold and its machine-word bounds, carry preservation,
and the composable-u52 output contract. The main theorem is
`radix51_mul_assembly_trace_correct`.

This is still not a complete binary proof. A bit-vector or ISA refinement must
connect the decoded x86 instruction stream to the checked scalar trace and
establish register allocation, eight-lane mapping, SysV clobbers, and the
load/store alias argument.

## Representation

Let `B = 2^51` and `p = 2^255 - 19`. A lane represents

```text
x[0] + x[1]B + x[2]B² + x[3]B³ + x[4]B⁴  (mod p).
```

Composable source limbs satisfy `0 <= x[i] < 2^52`. The representation is
redundant and is not necessarily canonical.

## Product split

For each 52-by-52-bit product, IFMA returns a low half `l` and high half `h`
such that

```text
product = l + 2^52 h = l + 2 h B.
```

The low half is accumulated at convolution degree `i+j`; twice the high half
is accumulated at degree `i+j+1`. This reconstructs the exact integer product.
The portable test oracle expresses this with `__uint128_t`, independently of
the native instruction schedule. `AssemblyTrace.lean` separately lists the
terms in the exact row-major update order; its prefix theorems prove that every
intermediate accumulator, not only the final sum, fits in u64.

## Reduction and bounds

Because `B^5 = 2^255 = 19 (mod p)`, degrees 5 through 9 fold into degrees 0
through 4 with coefficient 19. Under u52 inputs, each folded limb is below
`2^61`. Therefore multiplying a folded high coefficient by 19 fits in an
unsigned 64-bit word; the `VPMULLQ` low word is the exact integer product.

A parallel carry computes `c[i] = floor(t[i]/B)` from all five original folded
limbs, masks each limb to `B-1`, propagates `c[0..3]`, and folds `19*c[4]` into
limb zero. The raw-product bound gives `c[i] < 2^10`, so the result satisfies:

```text
out[0] < B + 19*1024
out[1..4] < B + 1024
```

Every output is consequently below `2^52` and can be reused by IFMA.

The Lean layer also proves the stronger generic weak-carry contract: if every
input is a genuine nonnegative u64 limb, one parallel carry still returns u52
limbs. The largest carry is below `2^13`, so limb zero remains below
`B + 19*8192 < 2^52`. This statement deliberately excludes signed values
encoded in two's complement.

## Lane independence

Every vector instruction is lane-wise. There are no permutes, horizontal
reductions, gathers indexed by another lane, or cross-lane masks. The field
kernel therefore computes eight independent field products. Higher-level
verdict code must preserve that property and is tested separately.

## Aliasing

All five limbs of both operands are loaded before the first output store.
Exact `out == x` and `out == y` aliasing are safe and covered by tests. Partial
overlap is deliberately excluded from the public contract.

## Required negative tests

- maximum legal u52 limbs;
- a single limb equal to `2^52`, rejected before native entry;
- independent random values in all eight lanes;
- exact source/output aliasing for each input;
- a deliberately perturbed fold constant, which must fail the oracle;
- native output compared bit-for-bit, not merely modulo `p`.
