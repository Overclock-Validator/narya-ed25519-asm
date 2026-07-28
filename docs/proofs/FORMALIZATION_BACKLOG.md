# Formalization backlog

The first useful machine-checked target is the r51×8 multiply contract, split
into two refinement layers:

1. a Lean theorem for split-product reconstruction, reduction modulo
   `2^255-19`, u64 no-wrap bounds, and the final u52 carry bound;
2. an instruction-level theorem or bitvector certificate connecting the
   SysV AVX-512 leaf to that scalar operation, including lane noninterference
   and load-before-store alias safety.

Later targets are the compressed decoder/small-order classifier, canonical-R
predicate, projective compressed-point equality, and the complete strict
verification equation. The broader question list and intended theorem
boundaries live in the Go source repository's
`docs/proofs/FORMALIZATION_BACKLOG.md`.

The next self-contained arithmetic target is the signed radix-2^21 reduction
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
