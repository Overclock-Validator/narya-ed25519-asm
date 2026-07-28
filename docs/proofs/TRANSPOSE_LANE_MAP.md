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

Equivalently, if `q` is the qword/coordinate index, `j` is the limb, and `i`
is the source lane, the byte containing that value in the arithmetic-SoA
output is

```text
projective: byte(320*q + 64*j + 8*i) = source[i]->limb[j][q]
affine:     byte(320*q + 64*j + 8*i) = source[i]->limb[j][q], q < 3
```

The source checker proves these address equalities directly for every emitted
load/store cell. It also proves that the 160 projective and 120 affine cells
are each written exactly once and remain within their 1,280- and 960-byte
destinations.

## Machine-checked lane theorem

[`Transpose.lean`](../../formal/lean/NaryaFormal/Transpose.lean) models the
EVEX.256 instructions used by the leaf:

- `VPUNPCKLQDQ(a,b) = [a0,b0,a2,b2]`;
- `VPUNPCKHQDQ(a,b) = [a1,b1,a3,b3]`;
- `VSHUFI64X2` immediate bit 0 selects the first source's 128-bit half;
- immediate bit 1 selects the second source's 128-bit half.

For EVEX.256 `VSHUFI64X2`, only immediate bits 0 and 1 participate in the
selection. Thus `0x00` selects both low halves and `0x03` selects both high
halves; higher immediate bits do not change the YMM result.

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
7. requires the complete function body to equal the expected prologue,
   invocations, and epilogue, so an inserted instruction fails closed; and
8. exhaustively verifies every output cell and address: 160 projective cells
   and 120 affine cells.

[`test_transpose_schedule_mutations.py`](../../tools/test_transpose_schedule_mutations.py)
demonstrates that representative changes to a shuffle immediate, lane-half
offset, pointer assignment, affine mask/load, output offset, or instruction
stream are all rejected.

The next binary-refinement layer is now committed as
[`GeneratedTransposeObjectBytes.lean`](../../formal/lean/NaryaFormal/GeneratedTransposeObjectBytes.lean).
`generate_transpose_object_bytes.py` extracts the exact STT_FUNC bytes from
the two ELF64 x86-64 objects and rejects any relocation section targeting
their executable sections. Because these leaves contain no link-time
references, those symbol bytes are link-stable. Lean kernel-checks both symbol
extents and that every literal is an octet in `TransposeObjectBytes.lean`.
This freezes the input for a restricted decoder. `TransposeX86Decoder.lean`
now decodes every one of the ten eight-instruction shuffle blocks in each
assembled symbol. It parses the VEX.256 unpack and EVEX.256 `VSHUFI64X2`
register operands and immediates, requires the exact vector length/prefix/map
forms used by the leaves, and proves that all twenty blocks equal the one
expected register schedule. A small generic register interpreter then proves
that schedule is the mathematical 4×4 transpose for arbitrary inputs and
arbitrary incoming scratch-register values.

The existing native selector tests provide a third layer: concrete unique
tags traverse table selection and the assembly leaf under all lane masks,
signs, and magnitudes. On Linux, the affine test additionally places each
120-byte source entry immediately before a `PROT_NONE` page. The final masked
load necessarily addresses a suppressed fourth qword in that guard page; a
masking or fault-suppression regression therefore faults the test process.

## Affine masked-tail obligation

Every affine row contains only three qwords. `K1=0b0111` makes qwords 0–2
active and qword 3 inactive on each `VMOVDQU64 {k1}{z}`. The fourth loaded
register element is used only as the unused fourth column of the common 4×4
shuffle and is never stored as an affine coordinate.

For the final row, the effective address of suppressed qword 3 is exactly one
entry length (120 bytes) from the source base and may be on the following
page. EVEX per-element fault suppression is therefore a correctness and
memory-safety precondition, not merely a performance detail. Architecturally,
the masked-off element must not raise a memory exception or update page
accessed/dirty state. This certificate deliberately makes no stronger
microarchitectural claim about bus transactions or cache activity.

The leaf requires AVX-512F, AVX-512VL, and AVX-512DQ for these encodings and
mask-register setup; the public CPU gate requires all three (along with IFMA
and the other backend features) before reaching it.

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
but it is not yet a whole-leaf execution proof over decoded ELF machine code.
Exact relocation-free assembled symbol bytes are pinned and every shuffle
block is decoded and semantically tied to the transpose theorem, but it still
trusts:

- the small Python source parser/interpreter;
- the stated Intel instruction semantics;
- the small ELF extractor until the bytes are decoded in Lean;
- the SysV AMD64 calling convention used by the source;
- valid, non-overlapping source/output objects as required by the internal ABI;
- the CPU's implementation of the instructions.

Closing the remaining binary-refinement gap requires decoding the surrounding
GPR pointer setup, masked/unmasked loads, output stores, `VZEROUPPER`, and
`RET`, then proving their byte-memory execution refines the source layout
trace. That larger obligation is tracked separately and must not be inferred
from the shuffle-block theorem.
