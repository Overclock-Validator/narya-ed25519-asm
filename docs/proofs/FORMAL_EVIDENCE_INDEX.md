# Formal evidence index

This is the shortest route from an audit question to the strongest checked
claim currently in the repository. A row marked **closed** has a Lean theorem
for the stated boundary. A row marked **partial** deliberately stops before a
larger claim. Specifications and conditional composition theorems are not
reported as completed implementation proofs.

`make check-formal-hygiene` requires every named audit anchor below to remain a
real declaration and rejects `sorry`, `admit`, custom `axiom`, and `sorryAx`
escapes anywhere in the Lean project. `make formal-check` then builds the pinned
Lean and mathlib project. This protects proof presence; it does not replace
review of theorem statements, generators, restricted x86 semantics, or the
trusted Lean toolchain.

| Question | Status | Machine-checked entry point | Exact boundary |
| --- | --- | --- | --- |
| Does the r51 IFMA product preserve multiplication modulo `2^255-19` and return reusable u52 limbs? | closed | `NaryaFormal.Radix51.AssemblyTrace.radix51_mul_assembly_trace_correct` | Exact generated 25-product scalar trace, u52 inputs, fold and carry; not by itself an instruction proof. |
| Do add, biased subtract, and biased negate preserve their field operations without unsigned underflow? | closed | `NaryaFormal.Radix51.LinearTrace.add_assembly_trace_correct`, `sub_assembly_trace_correct`, `neg_assembly_trace_correct` | Exact source-generated linear traces and composable-u52 contracts; emitted bytes are not yet decoded. |
| Do the canonical linked multiplier bytes decode to the source-generated instruction list? | closed | `NaryaFormal.X86.r51_object_decodes_to_source_instruction_trace` | Exact 800-byte proof ELF symbol and restricted decoder; not an arbitrary binary decoder or downstream link claim. |
| Does the decoded program's mathematical shadow compute the generated r51 result? | closed | `NaryaFormal.X86.runR51NatShadow_correct` | Full 129-instruction load-to-return Nat shadow; unbounded arithmetic, not machine no-wrap. |
| Does real 64-bit vector arithmetic refine the mathematical multiplier? | partial | `NaryaFormal.X86.run_arithmetic_core_refines` | All 94 decoded arithmetic instructions, arbitrary lane, explicit u52/no-wrap and constant-memory premises, with memory preservation. Input composition, return, full alias/frame, and SysV postconditions remain open; output stores are covered separately below. |
| Do the five decoded output stores preserve lane identity, write the proved limbs to the correct rows, and respect their byte frame? | closed | `NaryaFormal.X86.run_store_phase_refines` | Exact five-store suffix, explicit writable permissions, row isolation, read-back, register and permission preservation, and no writes outside the five 64-byte rows. |
| Can arbitrary entry values in temporary ZMM registers affect the decoded body before definition? | partial | `NaryaFormal.X86.decoded_body_definite_assignment`, `arithmetic_core_definite_assignment` | Exact syntactic dependency/write certificate. A semantic noninterference theorem connecting it to the machine refinement remains open. |
| Does either selector transpose preserve signature-to-lane identity? | partial | `NaryaFormal.Transpose.projective_transpose_x8_lane_exact`, `affine_transpose_x8_lane_exact` | Source-level shuffle semantics and lane map, paired with a fail-closed source checker. Emitted-opcode refinement remains open. |
| Is the radix-`2^21` group-order fold identity correct, and do local carries preserve represented integers? | partial | `NaryaFormal.ScalarReduction.fold_polynomial_exact`, `radix12_fold_mod_order` | Algebraic fold and local carry layer. Full 512-bit parse, canonical final range, packing, and assembly refinement remain open. |
| What would imply correctness of the scalar and x8 strict verifier? | specification | `NaryaFormal.VerificationSpine.verifyStrict_correct`, `verifyStrictX8_correct` | Conditional composition spine with explicit leaf hypotheses. It is intentionally not evidence that those hypotheses are discharged. |

## Trusted boundary

The strongest byte-linked result currently trusts:

- the pinned Lean compiler and mathlib dependency graph;
- the small Python source extractors and deterministic ELF-byte generator;
- the restricted decoder and instruction semantics implemented in Lean;
- the canonical proof link produced by the documented Clang/LLD pipeline; and
- reviewers to confirm that theorem statements capture the intended security
  and ABI claims.

It does **not** trust a hand-maintained instruction list: the exact linked bytes
are decoded independently and proved equal to the source-generated list. It
does not yet identify that proof ELF with every downstream deployment binary.
See [the assurance model](ASSURANCE_MODEL.md) and
[the byte-linked refinement plan](X86_OBJECT_REFINEMENT_PLAN.md) for the wider
boundary and remaining obligations.
