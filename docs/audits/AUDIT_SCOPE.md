# Audit scope

## Current checkpoint

The current reviewable scope contains a complete ABI-zero strict verifier:

- CPUID/XCR0 gate for the complete r51 feature set;
- checked r51×8 multiply/add/subtract/negate wrappers;
- SysV AVX-512 IFMA field leaves;
- fused raw-product/direct-XY doubling Stage-2, typed P2/P3 intermediate
  doubling, and a C projective-Niels addition schedule over reviewed leaves;
- permissive compressed-point decoder with pinned scalar-Go fixtures;
- SysV x8 rolling-register SHA-512 compression with scalar and FIPS oracles;
- canonical scalar reduction and exact signed radix-32 recoding;
- pre-signed projective-Niels table construction and assembly transpose;
- variable-base scalar multiplication, an immutable radix-256 basepoint comb,
  and complete `[S]B-[k]A` evaluation;
- canonical-S, exact small-order A/R, canonical-R, projective equality, and
  independent lane verdicts;
- scalar differential oracles and native Zen 5 evidence.

The fixed-base term uses the checked-in radix-256 comb and its independently
generated affine-Niels table. The table generator, binary payload, scalar
fixtures, native active-mask sweep, and checksummed Zen 5 execution record are
part of the current review boundary. These are correctness artifacts, not a
general performance claim.

## High-priority review questions

1. Are every IFMA source and accumulator bound sufficient and correctly tied
   to its call site?
2. Is `VPMULLQ` by 19 exact under the proved pre-fold bound?
3. Does every alias-safe leaf load all necessary data before any store?
4. Is the CPUID/XCR0 gate at least as strong as every instruction reachable
   after it?
5. Can any instruction, mask, or future transpose mix independent verdict
   lanes or mis-map a lane back to its caller index?
6. Does the decoder exactly implement the pinned permissive byte semantics,
   especially `y >= p` and `x = 0` with sign bit one?
7. Is explicit canonical-R plus decoded projective equality exactly equivalent
   to dalek 2.x's terminal compressed-byte comparison?
8. Does digit-level negation preserve exact signed-integer semantics for
   mixed-order public keys?
9. Do the doubling Stage-2 535/1068/1069 biases cover the exact raw-product
   ranges at every limb, and does the P2 schedule reconstruct `T` before
   every possible addition?

Question 5 now has a source-level Lean theorem and assembly-source certificate
covering both transpose leaves. Their exact relocation-free assembled symbol
bytes are pinned as Lean input, and every emitted shuffle block now decodes to
the proved 4×4 register schedule. Review still needs to confirm the restricted
shuffle semantics and ELF extractor. The surrounding pointer setup,
masked/unmasked loads, output stores, and return are not yet decoded/executed
as one whole-leaf Lean theorem.

The r51 multiply's arithmetic theorem now consumes a trace mechanically
generated from the assembly source. The extractor is fail-closed over the
straight-line leaf and has mutation tests for each major schedule class. A
separate fail-closed restricted decoder consumes the exact 800-byte symbol from
the canonical linked proof ELF, and Lean kernel reduction proves that it equals
the independently source-generated 129-instruction list. Audit must review both
parsers and the restricted instruction semantics. Whole-program execution in
the unbounded-natural shadow is now checked phase by phase and equals the
generated arithmetic trace. The decoded 94-instruction arithmetic core also
executes in the fault-aware BitVec machine and refines, under explicit u52,
no-wrap, and linked-constant memory premises, to that Nat trace in an arbitrary
lane. The decoded five-store suffix separately proves permission-sensitive
execution, exact row/lane read-back, disjoint-row preservation, and the exact
five-row byte-write frame from that post-arithmetic relation. Semantic
noninterference now connects the definite-assignment certificate to execution:
arbitrary caller values in ZMM28--31 cannot change any selected-lane output.
The exact ten-load/eighteen-clear prefix now also establishes the arithmetic
precondition from explicit readable source rows and arbitrary caller ZMM state.
The complete decoded leaf composes that prefix, the arithmetic core, stores,
`VZEROUPPER`, and `RET` with no source/output disjointness premise. Its final
theorem requires explicit output/return-slot disjointness, proves that the
entry return word survives the five stores, retains the mathematical output
and exact byte frame, advances RSP by eight, and returns to the entry word.
Identity with bytes in a downstream deployment, wrapper dispatch, and physical
CPU correctness remain open; this is not a general x86 decoder or a proof
about an arbitrary consumer binary.

The promoted doubling Stage-2 reuses the multiplier's raw arithmetic schedule,
but its fourfold expansion, expression-specific bias/carry layer, workspace
route, and P2 consumer are not covered by the multiplier's byte-linked theorem.
Review its source-level interval certificate and native adversarial tests as
separate evidence, then treat the dedicated Lean/refinement item in the
formalization backlog as open.

The SHA-512 leaf now has a fail-closed source certificate for every FIPS
constant, rotation, ternary truth table, rolling message word, working-register
rotation, and feed-forward store. Independent review must still validate that
model and close the assembled-binary and C padding-scheduler refinement gaps.

The scalar-reduction certificate now pins every one of its 60 macro calls,
including fold positions, carry adjacency, and the rounded-carry broadcast.
Negative tests reject each previously accepted route mutation. A Lean theorem
closes the canonical tail from the source-certified one-window checkpoint, but
the C parser/packer and signed 434-instruction assembled-byte refinement remain
open. See the dated scalar-reduction review follow-up for the exact boundary.

## Before release

The scope must expand to long native fuzz soaks, independent regeneration of
all byte classifiers, ABI-version review, fault containment, complete
performance artifacts, and at least one independent implementation audit.
RFC 8032, CCTV, Wycheproof, deterministic edge cases, committed fuzz seeds,
and fixed-base-comb evidence are checked in; their presence does not replace
the remaining independent review.
