# Field-arithmetic evidence handoff

This note is the shortest review path for an independent implementation team
evaluating Narya's five-limb radix-`2^51` IFMA arithmetic. It describes the
claim that is machine-checked, the remaining trust boundary, and the work
needed to adapt the idea to another radix or instruction schedule.

## Exact proved claim

Let `p = 2^255 - 19`, `B = 2^51`, and let each input be five nonnegative
limbs strictly below `2^52`. For one logical SIMD lane, the scalar trace
generated from `narya_r51x8_mul_ifma`:

1. accumulates all 25 products with `VPMADD52LUQ/HUQ` semantics;
2. rebases each high half using `2^52 = 2B`;
3. folds degrees 5 through 9 using `B^5 = 19 (mod p)`;
4. performs one parallel radix-`B` carry; and
5. returns five limbs strictly below `2^52` whose represented value is the
   input product modulo `p`.

Every low/high accumulator prefix, high-half shift, combined degree, `×19`
fold product, fold addition, and final carry is bounded so the modeled u64
instruction does not wrap.

The assembly source/model mirror is no longer manual. The fail-closed extractor
and generated Lean input are documented in
[`R51_SOURCE_TRACE_REFINEMENT.md`](R51_SOURCE_TRACE_REFINEMENT.md). The
end-to-end Lean theorem is
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
| Linear add/subtract/negate source traces | `add_assembly_trace_correct`, `sub_assembly_trace_correct`, `neg_assembly_trace_correct` |

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

`make formal-check` first requires byte equality between the generated Lean
trace and the assembly source, then checks the mathematical theorem over that
trace. `make check-source` also mutation-tests the extractor and asks Clang to
parse the GNU assembly for an x86-64 ELF target. Neither gate is an external
audit or an emitted-object proof.

Native tests additionally compare the exact redundant output limbs against an
independent `__uint128_t` oracle, exercise all eight lanes independently, test
exact input/output aliasing, and reject a source limb equal to `2^52`.

## What this does not prove

The Lean files do not decode an ELF object or execute a complete x86 semantics.
The source extractor checks the register schedule and rejects unmodeled source
instructions; the remaining refinement must connect emitted object bytes to
that checked source trace and cover:

- `VPMADD52LUQ/HUQ`, `VPMULLQ`, shifts, masks, and additions as bitvectors;
- the mapping of eight ZMM lanes to eight independent scalar traces;
- SysV register clobbers and constant loads;
- all-source-loads-before-output-stores alias safety; and
- the checked wrapper's CPU/OS feature gate and source-range validation.

The add, subtract, and negate leaves now have generated, fail-closed source
traces and Lean proofs of their exact `4p` biases, non-underflow, no-wrap,
modular semantics, and composable-u52 outputs. This covers only those leaves
under u52 inputs. Point-formula schedules and any fused or lazy-reduction
variants still require their own expression-specific certificates.

## What transfers to another radix-51 implementation

The proof separates reusable mathematics from implementation refinement. For
another five-limb radix-`2^51` implementation with u52 IFMA inputs:

| Component | Reusable result | Target-specific work |
| --- | --- | --- |
| 25-product low/high convolution | split, positioning, grouping, prefix bounds, modular fold | show the target trace contains the same terms and bounded prefixes |
| Loose product before carry | congruent product with every limb below `2^61` | connect the target's `×19` instruction sequence to exact integer multiplication |
| Parallel weak carry | preservation modulo `p`; any unsigned u64 input returns u52 limbs | prove shifts, masks, additions, and any IFMA carry fold refine the scalar operation |
| Dedicated squaring | only the identity `x*x` follows abstractly | prove the target's symmetry-reduced instruction trace and every doubled prefix |
| Canonical reduction | not covered | prove unique output in `[0,p)` and preservation modulo `p` |
| Add/subtract and point formulas | carry lemma only | prove non-underflow, no-wrap, and output bounds for each actual expression DAG |
| SIMD lanes and ABI | scalar theorem applies pointwise | prove lane mapping, absence of cross-lane operations, memory safety, and dispatch |

Consequently, this package can justify the arithmetic design and discharge
most of a matching multiplier proof. It must not be described as a proof of a
different source file or compiler output until the target-specific column is
completed.

## Lazy linear arithmetic needs expression bounds

A named state such as “wide below `2^62`” is not, by itself, a composability
certificate. That set is not closed under ordinary addition: two legal inputs
can sum to almost `2^63`. A subtraction bias of `k*p` is safe only when the
negative operand is bounded tightly enough that each radix limb of the bias
covers it, and the positive operand plus the bias still fits in u64.

For example, a bias with limbs approximately `2^61` cannot justify
subtraction for an arbitrary operand below `2^62`. It may still be correct for
a particular point-formula node whose negative input is a single raw product
below `2^61`; that narrower fact is what the certificate must state and prove.
Use per-limb intervals and distinguish unsigned values from signed values held
in two's complement. Do not infer closure from a descriptive type name.

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
4. Prove the dedicated square trace, linear operations, and every fused
   point-formula range schedule. Record per-node intervals rather than relying
   on one coarse “wide” bound.
5. Retain the mechanically generated source trace, and add object-code/ISA
   refinement so assembler or encoding divergence cannot evade it.
6. Differential-test on native Zen 4 and Zen 5 hardware, including maximum
   legal limbs, all lanes, exact aliasing, and mutations of every fold/bias
   constant.

The portable insight is the proof method and the value of one-bit source
headroom. The numeric certificate is specific to the radix, limb bounds, and
instruction order recorded here.
