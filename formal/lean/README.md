# Narya Lean formalization

This directory contains the machine-checked algebraic layer for Narya's
consensus-critical arithmetic. It is deliberately separate from the C and
assembly build: a successful Lean build proves the stated mathematical model,
not that an x86 instruction trace implements that model.

The first completed target is the five-limb radix-`2^51` field multiplier:

- exact reconstruction of a 52-bit IFMA low/high pair;
- positioning that pair in radix `2^51`;
- the `2^255 = 19 (mod p)` fold;
- ordinary carry preservation;
- the exact row-major 25-product accumulator trace;
- every low/high accumulator prefix, `COMBINE_HIGH`, and `×19` no-wrap bound;
- folded-limb, carry, and composable-u52 bounds;
- the more general unsigned weak-carry theorem from arbitrary u64 limbs to
  reusable u52 limbs.

The second completed source-level target is the x8 selector transpose:

- ISA-level models of the YMM `VPUNPCKLQDQ`, `VPUNPCKHQDQ`, and
  `VSHUFI64X2` operations used by the assembly;
- a generic theorem that the eight-instruction network is exactly a 4×4
  transpose;
- two-half x8 theorems for all projective and affine coordinates; and
- explicit treatment of the affine mask-zeroed fourth qword.

[`Radix51.lean`](NaryaFormal/Radix51.lean) contains the representation-level
algebra. [`AssemblyTrace.lean`](NaryaFormal/AssemblyTrace.lean) mirrors the
assembly's row-major `MUL_PAIR` order and degree grouping. Its main theorem,
`radix51_mul_assembly_trace_correct`, proves the modular product and reusable
u52 output contract from only the real source precondition: every input limb
is below `2^52`. The prior abstract folded-schedule hypothesis is discharged.

[`Transpose.lean`](NaryaFormal/Transpose.lean) contains the generic lane
theorems. `tools/check_transpose_schedule.py` binds those semantics to the
actual assembly source's macros, pointer map, five limb rows, and output
offsets. See the
[transpose certificate](../../docs/proofs/TRANSPOSE_LANE_MAP.md) for the exact
claim and trust boundary.

The remaining gap is binary/ISA refinement: proving that the assembled x86
instructions implement these source-level traces, plus SysV ABI checks and
load-before-store memory theorems. The Lean result is not a verified decoder
for arbitrary machine code and does not prove CPU dispatch.

The representation lemmas and most of the multiplication trace can be reused
by another radix-`2^51`, u52-input implementation. Such reuse still requires
an explicit mapping from that implementation's ordered operations to the
checked scalar trace. A symmetry-reduced square, canonical reducer, lazy
linear operation, or fused point formula is a different trace and is not
covered merely because it uses the same limb representation.

## Reproduce

The project pins Lean and mathlib. From this directory:

```sh
lake update
lake build
```

`lake-manifest.json` is committed after dependency resolution. `.lake/` is a
local build/cache directory and is ignored.
