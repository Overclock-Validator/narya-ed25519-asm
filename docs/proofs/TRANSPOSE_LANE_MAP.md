# x8 transpose lane-map certificate

The projective- and affine-Niels selectors change representation from eight
independent per-key records into field elements whose SIMD lanes hold those
eight keys. A lane-permutation error here could apply one signature's selected
point to another signature's scalar or return the verdict under the wrong
caller index. This document states the checked map and its assurance boundary.

## Required map

For every coordinate `c`, radix-51 limb `j`, and signature lane `i`, the
required output is

```text
output[c][j][i] = input[i][j][c].
```

The projective layout has four coordinates in each 32-byte source row:
`[Y+X, Y-X, Z, 2dT]`. The affine layout has three coordinates in each 24-byte
row: `[Y+X, Y-X, 2dT]`. Its assembly uses a zero-masked four-qword load, so the
same shuffle network sees `[Y+X, Y-X, 2dT, 0]`.

Each leaf processes sources 0–3 and 4–7 independently with YMM registers, then
stores the halves into lanes 0–3 and 4–7 of the destination field elements.
The operation repeats for all five limbs.

## Machine-checked lane theorem

[`Transpose.lean`](../../formal/lean/NaryaFormal/Transpose.lean) models the
EVEX.256 instructions used by the leaf:

- `VPUNPCKLQDQ(a,b) = [a0,b0,a2,b2]`;
- `VPUNPCKHQDQ(a,b) = [a1,b1,a3,b3]`;
- `VSHUFI64X2` immediate bit 0 selects the first source's 128-bit half;
- immediate bit 1 selects the second source's 128-bit half.

These are the 256-bit cases specified for `VSHUFI64X2` and the lane-local
unpack operations in Intel's *64 and IA-32 Architectures Software Developer's
Manual*, Volume 2C. The theorem `transpose4_schedule_exact` proves, for an
arbitrary value type, that the eight-instruction network equals the
mathematical 4×4 transpose. The projective and affine x8 theorems then prove
the complete two-half lane order. No finite test domain or arithmetic
property of the values is assumed.

## Binding the theorem to assembly source

[`check_transpose_schedule.py`](../../tools/check_transpose_schedule.py) reads
the actual two assembly files on every `make check-source` run. It:

1. parses and symbolically executes the instructions in each actual
   `TRANSPOSE_4X4` macro with the same ISA semantics as the Lean model;
2. rejects any instruction outside its deliberately small vocabulary;
3. requires the projective and affine shuffle macros to remain identical;
4. checks the exact masked/unmasked load and store templates;
5. checks the eight source-pointer-to-lane assignments;
6. checks all ten limb/half macro invocations; and
7. exhaustively verifies every output cell: 160 projective cells and 120
   affine cells.

The existing native selector tests provide a third layer: concrete unique
tags traverse table selection and the assembly leaf under all lane masks,
signs, and magnitudes.

## Exact conclusion

At the modeled source level, both transpose leaves preserve signature identity:

```text
projective: 4 coordinates × 5 limbs × 8 lanes
affine:     3 coordinates × 5 limbs × 8 lanes
```

No coordinate from source lane `i` is written to output lane `k` for `i != k`.
The affine masked load's fourth qword is zero and is not stored as a coordinate.

## Remaining trust boundary

This is stronger than a handwritten inspection and broader than a tagged test,
but it is not a proof over decoded ELF machine code. It trusts:

- the small Python source parser/interpreter;
- the stated Intel instruction semantics;
- the assembler's encoding of the checked source;
- valid, non-overlapping source/output objects as required by the internal ABI;
- the CPU's implementation of the instructions.

Closing the binary-refinement gap requires decoding the emitted instruction
bytes and proving their register/memory execution refines the Lean trace. That
larger obligation is tracked separately and must not be inferred from this
certificate.
