# Byte-linked x86-64 refinement plan

Narya's current Lean proofs are connected fail closed to the checked assembly
**source**. They do not yet prove that the bytes in a final linked artifact
execute that source trace. This document fixes the smallest credible boundary
for closing that gap without importing a general-purpose x86 formalization.

The target is a restricted, byte-linked x86-64 semantics specialized to the
straight-line System V leaf `narya_r51x8_mul_ifma`. The proof must consume the
final linked symbol and its resolved read-only constants, not a handwritten
instruction transcript and not merely a digest.

This repository ships a static archive, so it does not control the eventual
consumer link. `make check-r51-object-bytes` therefore creates a deterministic,
build-ID-free linked ELF as a **canonical proof artifact**. Its exact symbol
and constant bytes are committed in `GeneratedR51ObjectBytes.lean` and rebuilt
in Linux CI. A later consumer/deployment gate must separately establish that
the bytes actually loaded by a downstream binary are the proved bytes (or are
an address-relocated instance covered by an extended theorem).

## Architecture

One mechanically decoded instruction list feeds two interpreters:

1. an exact `BitVec 64` machine interpreter with byte-addressed memory,
   faults, vector state, `VZEROUPPER`, and `RET`; and
2. an unbounded-`Nat` shadow interpreter carrying the mathematical register
   values used by the existing source trace.

The main chain is:

```text
final linked bytes and constants
        -> restricted Lean decoder
        -> one checked instruction list
        -> BitVec execution refines Nat shadow execution
        -> decoded Nat trace equals GeneratedR51MulTrace
        -> radix51_mul_assembly_trace_correct
        -> System V memory/register/alias theorem
```

The proof must keep six obligations separate:

1. final artifact bytes decode to the claimed instructions and operands;
2. the used instruction semantics match the architectural definitions;
3. modular machine operations equal unbounded operations under the proved
   per-instruction range bounds;
4. the decoded register schedule equals the existing scalar trace;
5. byte layout and all eight qword lanes are mapped independently; and
6. entry, return, callee-saved registers, memory frame, faults, and aliasing
   satisfy the System V contract.

Field correctness is imported only after item 4. A digest or successful
source extraction does not discharge item 1.

## Restricted instruction subset

The initial decoder and semantics should reject every encoding outside the
forms present in the leaf. The supported subset is:

- `VMOVDQU64`, `VPBROADCASTQ`, and `VPXORQ`;
- `VPMADD52LUQ` and `VPMADD52HUQ`;
- `VPADDQ`, `VPSLLQ`, `VPSRLQ`, and `VPANDQ`;
- `VPMULLQ`;
- `VZEROUPPER`; and
- `RET`.

The decoder must verify EVEX vector length, element width, mask mode, extended
register fields, ModRM/SIB/displacements, and RIP-relative constant targets.
The canonical decoded operand order is `(dst, src1, src2)`, independent of
assembly syntax.

The instruction semantics are lane-wise over `Fin 8 -> BitVec 64`. In
particular, IFMA consumes only the low 52 source bits and performs its
destination addition modulo `2^64`. Existing prefix bounds are used to prove
that this modular result equals the intended natural-number addition at every
actual program point.

## Memory, aliasing, and ABI

Memory is byte addressed. That is necessary for little-endian qword loads,
unaligned 64-byte accesses, exact write framing, partial overlap, and `RET`
reading its address from `[RSP]`.

The System V precondition supplies `RDI=out`, `RSI=x`, `RDX=y`, readable input
ranges, a writable 320-byte output, a readable return address, the expected
code and constants, nonwrapping addresses, and u52 source limbs. It does not
require the source and destination ranges to be disjoint.

The decoded program property "all ten source-vector loads precede the first
output store" must imply snapshot semantics. The exported theorem should
therefore cover `out=x`, `out=y`, `x=y`, all three equal, and arbitrary partial
source/output overlap, while still excluding overlap with code, constants,
and the stack return address.

The postcondition records the exact 320 output bytes, no writes outside that
range, return to the original address with `RSP+8`, preservation of System V
callee-saved GPRs and untouched architectural state, and the exact architectural
effect of `VZEROUPPER`.

## Required milestones

1. **Implemented:** extract the canonical final-linked symbol bytes, symbol
   size, and resolved constant bytes into a generated Lean artifact, and
   reproduce them in Linux CI. The Python ELF extractor remains trusted.
2. **Implemented:** `X86Decoder.lean` fail-closed decodes the exact 800 symbol
   bytes, and `X86ObjectRefinement.lean` proves by kernel reduction that the
   result is the independently source-generated 129-instruction list.
3. **Partially implemented:** `X86VectorSemantics.lean` defines exact
   qword-lane semantics and generic bitvector-to-natural refinement lemmas for
   IFMA, add, shift, mask, and multiply. `X86Machine.lean` now adds
   byte-addressed little-endian memory, 512-bit vector layout, permission-aware
   `RET`, and exact `VZEROUPPER` state changes. Canonical-address/CET behavior
   and the full memory-frame/round-trip proofs remain open.
4. Compose those lemmas over the decoded list using the existing accumulator,
   fold, and carry bounds.
5. Prove the decoded Nat execution equals the generated 25-product source
   trace.
6. Add the complete ABI, memory-frame, lane-noninterference, and alias
   corollaries.
7. Regenerate and rebuild the Lean artifact in CI whenever the final binary
   changes.

Keep the theorems local to each schedule phase rather than one monolithic
symbolic-execution proof. A product, register, factor-two, factor-19, or carry
mutation should fail at the corresponding phase.

## Trust boundary after completion

The remaining trusted base would include the Lean kernel and core `Nat`/
`BitVec` definitions, the restricted decoder and instruction semantics,
human review of those semantics against the architecture, the System V model,
the artifact-extraction boundary (until replaced by a Lean ELF parser), and
the already checked arithmetic development. The assembler and linker need
not be trusted for arithmetic correctness because the theorem consumes their
final bytes.

The theorem would remain relative to the architectural instruction
specification and would not cover wrapper correctness, CPUID/XCR0 dispatch,
deployment identity, CPU implementation defects, concurrent memory mutation,
speculation, or the remainder of Ed25519 verification.

Normative references for reviewing the small semantics are the
[Intel Software Developer's Manual](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
and the
[System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/raw/master/x86-64-ABI/abi.pdf).
