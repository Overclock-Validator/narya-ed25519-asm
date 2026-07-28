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

The conditional composition theorem and shared abstraction rules are recorded
in [`REFINEMENT_SPINE.md`](REFINEMENT_SPINE.md). The point model is the full
Edwards group with integer scalar action, not the prime-order quotient, so
mixed-order inputs cannot disappear behind a `ZMod L` abstraction. A single
lane-projection obligation contains SIMD noninterference; the protocol theorem
remains scalar.

## 3. Native refinement

Assembly tests compare exact redundant representations—not only canonical
field values—where exactness is part of the next operation's range contract.
Instruction-level review covers register clobbers, lane movement, masks,
aliasing, and CPU feature assumptions.

For the r51 multiply, a fail-closed extractor now generates the Lean proof
input from the assembly source and rejects unmodeled statements. This closes
the hand-maintained source/model mirror. A separate restricted Lean decoder
consumes the exact 800-byte canonical linked symbol and kernel-checks that it
equals the independently expanded 129-instruction source trace. The decoded
program's unbounded-natural execution is proved equal to the generated
arithmetic result. Its 50-instruction product and 17-instruction combine phases
also have checked BitVec no-wrap/lane refinements. The same is now true of the
fold and normalize suffixes: their broadcasts use an explicit readable-memory
contract, and the 94-instruction arithmetic core has one fault-aware lane
refinement theorem with memory preservation. The exact five-store suffix now
has an additional byte-memory theorem: explicit permissions, correct row and
lane mapping, disjoint-row preservation, and exact read-back of the arithmetic
result, with no writes outside the five output rows. A relational execution
theorem also proves that arbitrary caller values in ZMM28--31 cannot affect any
of the five arithmetic outputs: ZMM28 and ZMM30 are overwritten before use,
while ZMM29 and ZMM31 are never dependencies. Input loads and accumulator clears
now separately refine explicit readable source rows into the partial register
relation required by that theorem. The complete decoded leaf now composes
preparation, arithmetic, stores, `VZEROUPPER`, and `RET` into one theorem. It
permits arbitrary source/output overlap because every source load precedes
every store, requires only the ABI-forbidden output/return-slot overlap to be
absent, preserves the entry return word through all five stores, retains the
exact output byte frame, and proves RSP+8 and return-to-entry-RIP behavior.
Downstream deployment identity, wrapper/dispatch refinement, concurrent
mutation, and physical-CPU correctness remain separate open obligations.

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
