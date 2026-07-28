# Narya Lean formalization

This directory contains the machine-checked algebraic layer for Narya's
consensus-critical arithmetic. It is deliberately separate from the C and
assembly build: a successful Lean build proves the stated mathematical model,
not that an x86 instruction trace implements that model.

The first target is the five-limb radix-`2^51` field multiplier:

- exact reconstruction of a 52-bit IFMA low/high pair;
- positioning that pair in radix `2^51`;
- the `2^255 = 19 (mod p)` fold;
- ordinary carry preservation;
- accumulator, folded-limb, carry, and composable-u52 bounds.

`radix51_mul_correct_of_folded_schedule` is the current composition theorem.
It proves the final modular product and reusable-u52 contract from one named
refinement hypothesis: that the assembly's grouped low/high accumulators
produce the modeled folded value with five u61 limbs. This avoids presenting
the unfinished instruction trace as if it were already machine-checked.

The x86 refinement, eight-lane map theorem, ABI checks, and load-before-store
memory theorem remain separate follow-up targets.

## Reproduce

The project pins Lean and mathlib. From this directory:

```sh
lake update
lake build
```

`lake-manifest.json` is committed after dependency resolution. `.lake/` is a
local build/cache directory and is ignored.
