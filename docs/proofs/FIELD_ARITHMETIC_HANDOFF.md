# Field-arithmetic evidence handoff

This note is the shortest review path for an independent implementation team
evaluating Narya's five-limb radix-`2^51` IFMA arithmetic. It describes the
claim that is machine-checked, the remaining trust boundary, and the work
needed to adapt the idea to another radix or instruction schedule.

## Exact proved claim

Let `p = 2^255 - 19`, `B = 2^51`, and let each input be five nonnegative
limbs strictly below `2^52`. For one logical SIMD lane, the scalar trace
mirroring `narya_r51x8_mul_ifma`:

1. accumulates all 25 products with `VPMADD52LUQ/HUQ` semantics;
2. rebases each high half using `2^52 = 2B`;
3. folds degrees 5 through 9 using `B^5 = 19 (mod p)`;
4. performs one parallel radix-`B` carry; and
5. returns five limbs strictly below `2^52` whose represented value is the
   input product modulo `p`.

Every low/high accumulator prefix, high-half shift, combined degree, `×19`
fold product, fold addition, and final carry is bounded so the modeled u64
instruction does not wrap.

The end-to-end Lean theorem is
[`radix51_mul_assembly_trace_correct`](../../formal/lean/NaryaFormal/AssemblyTrace.lean).
Its only arithmetic hypotheses are the two input u52 contracts. The theorem
does not assume the grouped fold is correct; that obligation is discharged by
the exact 25-product trace in the same file.

## Proof map

| Obligation | Checked result |
| --- | --- |
| IFMA low/high reconstruction | `ifma_split_exact`, `ifma_split_radix51` |
| Product positioning | `positioned_ifma_split_exact` |
| Full 25-product convolution | `split_convolution_exact` |
| Exact assembly grouping | `grouped_convolution_exact` |
| Every IFMA accumulator prefix fits u64 | `low_accumulator_prefix_u64`, `high_accumulator_prefix_u64` |
| High-half shift and combined degrees fit u64 | `high_accumulator_shift_u64`, `grouped_degree_u64` |
| Degree-5 modular fold | `folded_grouped_preserves_mod` |
| Fold multiply/add no-wrap | `fold_products_u64`, `folded_grouped_u61` |
| Final IFMA carry fold is exact | `final_carry_ifma_low_exact` |
| Parallel carry preserves the residue | `parallel_carry_preserves_mod` |
| Outputs are reusable u52 sources | `normalized_limbs_u52` |
| Any unsigned u64 loose limbs weak-carry to u52 | `normalized_limbs_u52_of_u64` |
| End-to-end scalar trace | `radix51_mul_assembly_trace_correct` |

The representation-level lemmas live in
[`Radix51.lean`](../../formal/lean/NaryaFormal/Radix51.lean). The ordered trace
and its machine-word bounds live in
[`AssemblyTrace.lean`](../../formal/lean/NaryaFormal/AssemblyTrace.lean).
There are no `sorry`, `admit`, or project-defined axiom declarations in these
files.

## Reproduce

The repository pins Lean and mathlib. From the repository root:

```sh
make formal-check
make check-source
```

`make formal-check` checks the mathematical trace. `make check-source` asks
Clang to parse the GNU assembly for an x86-64 ELF target. These are distinct
gates and neither should be represented as an external audit.

Native tests additionally compare the exact redundant output limbs against an
independent `__uint128_t` oracle, exercise all eight lanes independently, test
exact input/output aliasing, and reject a source limb equal to `2^52`.

## What this does not prove

The Lean files do not decode an ELF object or execute an x86 semantics. The
remaining refinement must connect the assembled instructions and register
allocation to the scalar trace and cover:

- `VPMADD52LUQ/HUQ`, `VPMULLQ`, shifts, masks, and additions as bitvectors;
- the mapping of eight ZMM lanes to eight independent scalar traces;
- SysV register clobbers and constant loads;
- all-source-loads-before-output-stores alias safety; and
- the checked wrapper's CPU/OS feature gate and source-range validation.

The add, subtract, and negate leaves reuse the proved parallel carry and have
portable exact-output tests, but their complete ordered traces and bias bounds
have not yet been formalized in Lean. Point-formula schedules and any fused or
lazy-reduction variants require their own composability certificates.

## Radix-52 is a separate instantiation

This proof must not be cited as a proof of a five-limb radix-`2^52`
implementation.

For `B52 = 2^52`:

```text
2^52 = B52
B52^5 = 2^260 = 608 (mod 2^255-19)
```

Therefore an IFMA high half advances one radix degree with coefficient `1`,
not `2`, while degrees at or above five fold with coefficient `608`, not `19`.
Top-limb bounds, folded-degree bounds, carry placement, and the composable
output contract all change. A radix-52 implementation can reuse the proof
architecture, but it needs a new trace instantiated from its actual schedule.

## Recommended adoption sequence

1. Decide whether the target is this exact radix-51 schedule or a radix-52
   design. Do not mix their constants or range contracts.
2. Freeze the proposed multiply trace and derive every accumulator-prefix,
   fold-product, fold-addition, and carry bound from that trace.
3. Check exact redundant outputs against an independent big-integer or
   `__uint128_t` oracle; modulo-only comparison is insufficient for a
   composable range contract.
4. Prove the linear operations and every fused point-formula range schedule.
5. Add an object-code/ISA refinement or a mechanically generated trace check
   so an assembly edit cannot silently diverge from the proof model.
6. Differential-test on native Zen 4 and Zen 5 hardware, including maximum
   legal limbs, all lanes, exact aliasing, and mutations of every fold/bias
   constant.

The portable insight is the proof method and the value of one-bit source
headroom. The numeric certificate is specific to the radix, limb bounds, and
instruction order recorded here.
