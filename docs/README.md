# Documentation index

Documents are grouped by claim type. A benchmark does not prove correctness;
an algebraic derivation does not prove the machine code implements it; and a
passing differential corpus does not establish a universal theorem.

## Architecture

- [Standalone port plan](architecture/PORTING_PLAN.md)
- [System V ABI and data layouts](architecture/ABI.md)
- [Eight-lane SHA-512 compression](architecture/SHA512_X8.md)
- [Exact signed scalar recoding](architecture/SCALAR_RECODING.md)

## Proofs and assurance

- [Assurance model](proofs/ASSURANCE_MODEL.md)
- [r51 field contract](proofs/R51_FIELD_CONTRACT.md)
- [Scalar-reduction contract](proofs/SCALAR_REDUCTION_CONTRACT.md)
- [Formalization backlog](proofs/FORMALIZATION_BACKLOG.md)

## Audits and security review

- [Audit scope](audits/AUDIT_SCOPE.md)

## Performance

- [Benchmarking rules](performance/BENCHMARKING.md)

## Reproducibility

Each dated directory contains raw output, environment, commands, and a checksum
manifest. A result applies only to the source commit and scope it names.

- [Zen 5 field/point checkpoint, 2026-07-27](reproducibility/zen5-field-point-2026-07-27/README.md)
- [Zen 5 point/decode checkpoint, 2026-07-27](reproducibility/zen5-decode-2026-07-27/README.md)
- [Zen 5 hash/reduction checkpoint, 2026-07-27](reproducibility/zen5-hash-reduce-2026-07-27/README.md)
