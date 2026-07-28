# Assurance model

The project treats assurance as several linked but non-substitutable layers.

## 1. Protocol predicate

The library states the accepted byte language: canonical scalar,
permissive public-key decoding, original bytes in the challenge hash,
canonical signature-point encoding, pure small-order A/R rejection, and the
cofactorless verification equation. The checked-in external corpus is
differentially matched to the pinned Go Narya `DalekStrict` oracle; that
finite comparison is evidence, not a universal proof of equivalence.

## 2. Algebraic model

Scalar reference code states field and group operations without SIMD or
machine-register concerns. Formal notes prove congruence and range claims.

## 3. Native refinement

Assembly tests compare exact redundant representations—not only canonical
field values—where exactness is part of the next operation's range contract.
Instruction-level review covers register clobbers, lane movement, masks,
aliasing, and CPU feature assumptions.

For the r51 multiply, a fail-closed extractor now generates the Lean proof
input from the assembly source and rejects unmodeled statements. This closes
the hand-maintained source/model mirror. Emitted-object decoding and full x86,
ABI, and dispatch refinement remain separate open obligations.

## 4. Differential and adversarial testing

Required corpora include RFC vectors, CCTV, Wycheproof, permissive aliases,
small-order encodings, invalid decompressions, scalar boundaries, every lane
position, every active mask, and mutations around every special constant.
Deterministic fuzz seeds are committed. Long native fuzz runs must be
preserved as checksummed evidence before a reviewed release.

## 5. Hardware execution

GNU assembly parsing or emulation is insufficient. Promoted paths execute on
at least Zen 4 and Zen 5. Unsupported-CPU behavior is tested separately. SDE
can add regression coverage but is not performance evidence.

## 6. Independent review

This repository remains unaudited until external reviewers have examined the
protocol mapping, scalar oracles, native arithmetic, CPU dispatch, public ABI,
and build/release process. Passing project-owned tests is not an audit.
