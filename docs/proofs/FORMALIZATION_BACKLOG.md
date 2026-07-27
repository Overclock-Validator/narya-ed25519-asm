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
