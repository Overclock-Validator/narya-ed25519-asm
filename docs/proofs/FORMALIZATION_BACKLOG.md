# Formalization backlog

The first machine-checked target, the scalar trace of the r51×8 multiply,
is complete under [`formal/lean`](../../formal/lean/README.md). The checked
lemmas cover split-product reconstruction, the exact row-major accumulator
grouping, every partial accumulator bound, `COMBINE_HIGH`, the modular fold
and its no-wrap bounds, carry preservation, and the final u52 contract.

The remaining native multiplier work is one refinement layer:

1. add an instruction-level theorem or bitvector certificate connecting the
   SysV AVX-512 leaf to that scalar operation, including lane noninterference
   and load-before-store alias safety.

The selector transpose's source-level lane map is now machine checked in
`NaryaFormal.Transpose`, and a fail-closed source parser checks the actual
assembly macros, pointer assignments, limb invocations, and output offsets.
The remaining transpose obligation is the same binary-refinement layer:
decode the emitted instructions and connect their register/memory trace to the
proved source model. See [`TRANSPOSE_LANE_MAP.md`](TRANSPOSE_LANE_MAP.md).

Before treating the complete r51 field layer as formally covered, add two
generic trace families that are also useful to independent implementations:

1. a symmetry-reduced square trace proving the diagonal/cross-product
   reconstruction, every doubled accumulator prefix, the fold, and its loose
   output bound; and
2. per-expression linear certificates for add, negate, and biased subtract,
   including the exact maximum negative operand covered by each bias.

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
