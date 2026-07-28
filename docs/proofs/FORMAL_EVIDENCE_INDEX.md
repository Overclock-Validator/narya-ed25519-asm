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
| Does real 64-bit vector arithmetic refine the mathematical multiplier? | closed | `NaryaFormal.X86.run_arithmetic_core_refines` | All 94 decoded arithmetic instructions, arbitrary lane, explicit u52/no-wrap and constant-memory premises, with memory preservation. This is the local core result; the complete leaf is covered below. |
| Do the decoded source loads and accumulator clears establish the arithmetic-core precondition from arbitrary caller ZMM state? | closed | `NaryaFormal.X86.run_prepare_phase` | Exact ten-load/eighteen-clear prefix, selected lane, explicit readable rows and little-endian limb values, with memory/GPR preservation. Whole-body and return composition remain separate. |
| Do the five decoded output stores preserve lane identity, write the proved limbs to the correct rows, and respect their byte frame? | closed | `NaryaFormal.X86.run_store_phase_refines` | Exact five-store suffix, explicit writable permissions, row isolation, read-back, register and permission preservation, and no writes outside the five 64-byte rows. |
| Can arbitrary entry values in temporary ZMM registers affect the decoded arithmetic result? | closed | `NaryaFormal.X86.run_arithmetic_core_ignores_undefined_scratch` | Exact 94-instruction core, arbitrary selected lane, arbitrary entry values in ZMM28--31. It composes the dependency certificate with relational machine execution and proves the five output registers equal the sanitized mathematical execution. |
| Does the complete non-returning decoded body compose those phases with source/output aliasing? | closed | `NaryaFormal.X86.run_decoded_body_refines` | Exact load/clear/arithmetic/store body, selected lane, no source/output disjointness premise, mathematical output rows, GPR/permission preservation, and no writes outside the five output rows. `VZEROUPPER; RET` remains separate. |
| Does the exact epilogue implement `VZEROUPPER; RET` and normal System V return effects? | closed | `NaryaFormal.X86.run_expected_program_after_body` | Exact decoded suffix and composition after any successful body: memory preservation, RSP+8, return RIP, other-GPR preservation, and architectural ZMM effect. |
| Does the complete decoded multiplier leaf refine the mathematical result and its System V memory/return contract? | closed | `NaryaFormal.X86.run_r51_multiplier_refines` | Exact 129-instruction canonical proof symbol, arbitrary selected lane, explicit source/constant/output/return permissions, arbitrary source/output overlap, output/return-slot disjointness, exact five-row frame, non-RSP GPR preservation, RSP+8, and entry return RIP. It does not prove wrapper dispatch, downstream deployment identity, concurrent memory, or physical CPU correctness. |
| Does either selector transpose preserve signature-to-lane identity? | partial | `NaryaFormal.Transpose.projective_transpose_x8_lane_exact`, `affine_transpose_x8_lane_exact` | Source-level shuffle semantics and lane map, paired with a fail-closed source checker and exact relocation-free assembled-symbol byte artifacts. Decoding and execution refinement of those bytes remain open. |
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
