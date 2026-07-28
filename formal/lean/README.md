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
- folded-limb, carry, and composable-u52 bounds.

[`Radix51.lean`](NaryaFormal/Radix51.lean) contains the representation-level
algebra. [`AssemblyTrace.lean`](NaryaFormal/AssemblyTrace.lean) mirrors the
assembly's row-major `MUL_PAIR` order and degree grouping. Its main theorem,
`radix51_mul_assembly_trace_correct`, proves the modular product and reusable
u52 output contract from only the real source precondition: every input limb
is below `2^52`. The prior abstract folded-schedule hypothesis is discharged.

The remaining gap is binary/ISA refinement: proving that the assembled x86
instructions implement this scalar trace, plus the eight-lane map theorem,
SysV ABI checks, and load-before-store memory theorem. The Lean result is not
a verified decoder for arbitrary machine code and does not prove CPU dispatch.

## Reproduce

The project pins Lean and mathlib. From this directory:

```sh
lake update
lake build
```

`lake-manifest.json` is committed after dependency resolution. `.lake/` is a
local build/cache directory and is ignored.
