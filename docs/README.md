# Documentation index

Documents are grouped by claim type. A benchmark does not prove correctness;
an algebraic derivation does not prove the machine code implements it; and a
passing differential corpus does not establish a universal theorem.

## Suggested reading paths

- **Library user:** root `README.md` → architecture/ABI → strict predicate →
  security policy.
- **Independent auditor:** assurance model → audit scope → strict predicate →
  field and scalar contracts → native source and tests.
- **Arithmetic implementer:** field-arithmetic handoff → r51 contract → Lean
  source → formalization backlog.
- **Performance reviewer:** benchmarking rules → one dated reproducibility
  directory → the exact source commit named by that directory.

Files under `docs/proofs/` distinguish proved statements from specifications
and open obligations. Files under `docs/reproducibility/` are evidence of a
particular run, never general performance or correctness claims.

## Architecture

- [Standalone port plan](architecture/PORTING_PLAN.md)
- [System V ABI and data layouts](architecture/ABI.md)
- [Eight-lane SHA-512 compression](architecture/SHA512_X8.md)
- [Exact signed scalar recoding](architecture/SCALAR_RECODING.md)
- [x8 point-doubling schedule](architecture/POINT_DOUBLING.md)
- [Coordinate-packed n=1/n=2 verifier](architecture/PACKED_SMALL_BATCH.md)
- [Projective/affine-Niels addition schedule](architecture/NIELS_ADDITION.md)
- [Projective-Niels table and selector](architecture/PROJECTIVE_NIELS_TABLE.md)
- [Variable-base scalar multiplication](architecture/VARIABLE_SCALAR_MULTIPLICATION.md)
- [Merged asymmetric fixed-base schedule](architecture/ASYMMETRIC_FIXED_B10.md)
- [Exact cross-group batch finalization](architecture/BATCH_FINALIZATION.md)
- [Immutable fixed-base comb](architecture/FIXED_BASE_COMB.md)
- [Strict verification predicate](architecture/STRICT_PREDICATE.md)

## Proofs and assurance

- [Assurance model](proofs/ASSURANCE_MODEL.md)
- [Formal evidence index](proofs/FORMAL_EVIDENCE_INDEX.md)
- [r51 field contract](proofs/R51_FIELD_CONTRACT.md)
- [r51 multiply assembly-source refinement](proofs/R51_SOURCE_TRACE_REFINEMENT.md)
- [Byte-linked x86-64 refinement plan](proofs/X86_OBJECT_REFINEMENT_PLAN.md)
- [Field-arithmetic evidence handoff](proofs/FIELD_ARITHMETIC_HANDOFF.md)
- [Machine-checked radix-51 Lean layer](../formal/lean/README.md)
- [Scalar-reduction contract](proofs/SCALAR_REDUCTION_CONTRACT.md)
- [x8 transpose lane-map certificate](proofs/TRANSPOSE_LANE_MAP.md)
- [SHA-512 x8 source-schedule certificate](proofs/SHA512_SOURCE_SCHEDULE.md)
- [Formalization backlog](proofs/FORMALIZATION_BACKLOG.md)

## Audits and security review

- [Auditor quickstart](audits/AUDITOR_QUICKSTART.md)
- [Audit scope](audits/AUDIT_SCOPE.md)
- [Scalar-reduction review follow-up, 2026-07-28](audits/SCALAR_REDUCTION_REVIEW_2026-07-28.md)

## Performance

- [Benchmarking rules](performance/BENCHMARKING.md)
- [Open optimization investigations](performance/OPEN_OPTIMIZATIONS.md)

## Reproducibility

Each dated directory contains raw output, environment, commands, and a checksum
manifest. A result applies only to the source commit and scope it names.

- [Zen 5 field/point checkpoint, 2026-07-27](reproducibility/zen5-field-point-2026-07-27/README.md)
- [Zen 5 point/decode checkpoint, 2026-07-27](reproducibility/zen5-decode-2026-07-27/README.md)
- [Zen 5 hash/reduction checkpoint, 2026-07-27](reproducibility/zen5-hash-reduce-2026-07-27/README.md)
- [Zen 5 variable-scalar checkpoint, 2026-07-27](reproducibility/zen5-variable-scalar-2026-07-27/README.md)
- [Zen 5 complete strict-verifier checkpoint, 2026-07-27](reproducibility/zen5-strict-verifier-2026-07-27/README.md)
- [Zen 5 fixed-base-comb checkpoint, 2026-07-27](reproducibility/zen5-fixed-base-comb-2026-07-27/README.md)
- [Zen 5 decoder square-chain A/B, 2026-07-28](reproducibility/zen5-decoder-square-chain-2026-07-28/README.md)
- [Zen 5 fused doubling Stage-2/P2 A/B, 2026-07-29](reproducibility/zen5-doubling-stage2-p2-2026-07-29/README.md)
- [Zen 5 fused Niels Stage-2 A/B, 2026-07-29](reproducibility/zen5-niels-stage2-2026-07-29/README.md)
- [Zen 5 merged asymmetric B10 A/B, 2026-07-29](reproducibility/zen5-asymmetric-b10-2026-07-29/README.md)
- [Zen 5 cross-group batch finalizer A/B, 2026-07-29](reproducibility/zen5-batch-finalization-2026-07-29/README.md)
- [Zen 5 coordinate-packed n=1/n=2 checkpoint, 2026-07-29](reproducibility/zen5-packed-small-2026-07-29/README.md)
