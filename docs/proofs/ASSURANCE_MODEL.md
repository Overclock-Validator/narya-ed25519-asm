# Assurance model

The project treats assurance as several linked but non-substitutable layers.

## 1. Protocol predicate

The complete library will state the accepted byte language: canonical scalar,
permissive public-key decoding, original bytes in the challenge hash,
canonical signature-point encoding, pure small-order A/R rejection, and the
cofactorless verification equation. This must be differentially matched to the
pinned Go Narya `DalekStrict` oracle.

## 2. Algebraic model

Scalar reference code states field and group operations without SIMD or
machine-register concerns. Formal notes prove congruence and range claims.

## 3. Native refinement

Assembly tests compare exact redundant representations—not only canonical
field values—where exactness is part of the next operation's range contract.
Instruction-level review covers register clobbers, lane movement, masks,
aliasing, and CPU feature assumptions.

## 4. Differential and adversarial testing

Required corpora include RFC vectors, CCTV, Wycheproof, permissive aliases,
small-order encodings, invalid decompressions, scalar boundaries, every lane
position, every active mask, and mutations around every special constant.
Fuzz seeds are committed; long native fuzz runs are preserved as checksummed
evidence.

## 5. Hardware execution

GNU assembly parsing or emulation is insufficient. Promoted paths execute on
at least Zen 4 and Zen 5. Unsupported-CPU behavior is tested separately. SDE
can add regression coverage but is not performance evidence.

## 6. Independent review

This repository remains unaudited until external reviewers have examined the
protocol mapping, scalar oracles, native arithmetic, CPU dispatch, public ABI,
and build/release process. Passing project-owned tests is not an audit.
