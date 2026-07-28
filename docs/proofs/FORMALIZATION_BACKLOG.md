# Formalization backlog

The first machine-checked target, the scalar trace of the r51×8 multiply,
is complete under [`formal/lean`](../../formal/lean/README.md). The checked
lemmas cover split-product reconstruction, the exact row-major accumulator
grouping, every partial accumulator bound, `COMBINE_HIGH`, the modular fold
and its no-wrap bounds, carry preservation, and the final u52 contract.

The formal targets now share a capstone convention defined in
[`REFINEMENT_SPINE.md`](REFINEMENT_SPINE.md). `VerificationSpine.lean` states
conditional scalar and x8 `iff` theorems for the complete strict predicate.
Every unfinished leaf is an explicit typed hypothesis, the point abstraction
uses the full Edwards group with integer scalar action, and SIMD proof work is
isolated to one lane-projection obligation. New proofs should discharge those
hypotheses rather than introduce parallel, incompatible abstractions.

The multiply assembly source is now connected to the theorem by the generated,
fail-closed trace described in
[`R51_SOURCE_TRACE_REFINEMENT.md`](R51_SOURCE_TRACE_REFINEMENT.md). A source
edit changes a Lean proof input or fails extraction. The exact 800-byte
canonical linked multiplier now also kernel-decodes to the independently
expanded 129-instruction source trace. Its 94-instruction arithmetic core now
has a fault-aware BitVec-to-Nat lane refinement, including the linked fold and
mask constants. The remaining native multiplier work is memory and ABI
refinement:

1. compose the input loads, proved output-store suffix, epilogue, and arithmetic
   core into the full SysV memory, alias, return, and register postcondition in
   [`X86_OBJECT_REFINEMENT_PLAN.md`](X86_OBJECT_REFINEMENT_PLAN.md).

The paired interpreters and local arithmetic refinement lemmas now exist.
They expose every u52/no-wrap premise rather than assuming machine arithmetic
is unbounded. The generated instruction list is partitioned into eight checked
semantic phases. Small phase theorems now prove every unbounded register
transition from input loads through the returned stored output, and
`runR51NatShadow_correct` composes them into the exact decoded-program result.
This closes the decoded Nat schedule. The BitVec/Nat arithmetic item is now
also closed across product, combine, fold, and normalize: all 94 instructions
refine the exact Nat states in an arbitrary selected lane, and the constant
broadcasts are tied to an explicit read-only-memory contract. Semantic scratch
independence is also closed: a relational machine theorem proves arbitrary
entry values in ZMM28--31 cannot affect the five outputs. Input-memory
preparation is now closed separately across the exact ten loads and eighteen
clears, with explicit row permissions and selected-lane values. The
non-returning decoded body is now composed without a
source/output disjointness premise and preserves the exact five-row byte frame;
the exact `VZEROUPPER; RET` semantics and normal-return composition are also
closed. The remaining native step is deriving post-store return-slot
readability/value from an explicit stack/output non-overlap contract. The
five-store suffix's permissions, row isolation, selected-lane content, and
exact byte frame are now closed in `X86MemoryRefinement.lean`. A prior
monolithic 129-step
simplifier proof type-checked but was intentionally rejected because its
serialized proof term was too large for a dependable audit/CI artifact.

The add, subtract, and negate leaves now have the same fail-closed source-link
property. `GeneratedR51LinearTrace.lean` mirrors their exact instruction
shapes and constants, while `LinearTrace.lean` proves non-underflow, u64
no-wrap, modular semantics, and reusable-u52 outputs. Representative opcode,
operand, bias, normalization, and output mutations are rejected in CI.

The selector transpose's source-level lane map is now machine checked in
`NaryaFormal.Transpose`, and a fail-closed source parser checks the actual
assembly macros, pointer assignments, limb invocations, and output offsets.
The remaining transpose obligation is the same binary-refinement layer:
decode the emitted instructions and connect their register/memory trace to the
proved source model. See [`TRANSPOSE_LANE_MAP.md`](TRANSPOSE_LANE_MAP.md).

Before treating the complete r51 field layer as formally covered, add one
generic trace family that is also useful to independent implementations:

1. a symmetry-reduced square trace proving the diagonal/cross-product
   reconstruction, every doubled accumulator prefix, the fold, and its loose
   output bound.

The generic u52-input linear leaves are now closed. Fused point-formula
expressions with wider inputs remain separate obligations: each must prove the
exact maximum negative operand covered by its bias and its own output bounds.

Do not model these with one nominal “wide” state. Two values below `2^62` can
sum above `2^62`, and a bias near `2^61` does not cover an arbitrary operand
below `2^62`. The theorem hypotheses must preserve the actual per-limb
intervals from the point-formula DAG.

Later targets are the compressed decoder/small-order classifier, canonical-R
predicate, projective compressed-point equality, and the complete strict
verification equation. The broader question list and intended theorem
boundaries live in the Go source repository's
`docs/proofs/FORMALIZATION_BACKLOG.md`.

After those field-layer traces, the next self-contained arithmetic target is
the signed radix-2^21 reduction
of a 512-bit hash modulo the group order. Its exact statement and machine
obligations are recorded in
[`SCALAR_REDUCTION_CONTRACT.md`](SCALAR_REDUCTION_CONTRACT.md).

Keep this target split into four layers rather than proving one monolithic
packing statement:

1. exact 512-bit parsing, including the 29-bit top input coefficient;
2. modular preservation by folds and exact centered/ordinary carries;
3. direct canonical range `0 <= Y < l`, allowing output bit 252;
4. instruction and wrapper refinement, including per-instruction signed
   bounds, logical-lane mapping, arbitrary input/output overlap, and error
   atomicity.

The intended named lemmas are listed in the scalar-reduction contract. Add
the deterministic `l-1`/bit-252 and carry-boundary regressions before treating
an automated certificate as complete.

The assembly-source interval/no-wrap layer is now executable in
`tools/check_scalar_reduce_bounds.py`: all 389 arithmetic intermediates stay
within signed 64-bit range and the widest bound is 49 bits. This closes that
source-level safety item under the parser's stated initial bounds. It does not
close `parse_radix21_correct`, `final_value_canonical`, `pack32_exact`, or
assembled-opcode refinement. In particular, independent final intervals leave
limb 11 in `[-1, 2^21]`; the canonical theorem requires relational reasoning.

After that arithmetic seam, formalize the variable-base scalar multiplier as
a composition theorem rather than another instruction proof:

1. the 51 balanced radix-32 digits reconstruct the exact signed integer, not
   merely a residue modulo the scalar order;
2. each positive/negative micro-AoS entry represents the requested signed
   multiple of its lane's base point;
3. the Horner schedule of five doublings between rounds returns `[k]P` or
   `[-k]P` for every canonical scalar;
4. lane masking replaces only inactive/invalid lanes with the identity and
   cannot affect any active lane.

This target can reuse an abstract Edwards group and does not need to model
AVX-512 instructions. The instruction-refinement proof remains localized to
the field and transpose leaves.

The fixed-base comb admits an even smaller abstract-group proof. Establish
that 32 balanced radix-256 digits reconstruct `s`, define
`P_i=[2^(16i)]B`, and prove that accumulating odd columns, multiplying the
result by `2^8`, then accumulating even columns equals `[s]B`. Separately
prove that each generated table record is the affine-Niels representation of
`[m]P_i` for `m in 1..128`; the binary-to-assembly obligation is its pinned
   SHA-256 plus the three-coordinate transpose refinement.

The SHA-512 assembly's full source schedule is now mechanically checked against
FIPS 180-4 by `tools/check_sha512_schedule.py`, including rolling `a..h` and
`W[t mod 16]` maps. Remaining formal work is emitted-opcode refinement and a
wrapper theorem for byte gathering, big-endian words, padding/length encoding,
unequal-lane completion, and digest capture.
