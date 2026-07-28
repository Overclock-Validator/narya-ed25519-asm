# Narya Lean formalization

This directory contains the machine-checked algebraic and restricted-machine
layers for Narya's consensus-critical arithmetic. A successful Lean build now
proves that the exact multiplier bytes in the canonical proof ELF decode to the
independently source-generated trace, in addition to the mathematical claims
below. It does not yet prove the complete execution/ABI refinement, identity
with a downstream binary, or correctness of a physical processor.

Auditors can begin with the repository's
[formal evidence index](../../docs/proofs/FORMAL_EVIDENCE_INDEX.md), which maps
the stable capstone theorem names to their exact claim boundaries. CI runs
`make check-formal-hygiene` before the build to reject proof placeholders and
missing audit anchors.

The first completed target is the five-limb radix-`2^51` field multiplier:

- exact reconstruction of a 52-bit IFMA low/high pair;
- positioning that pair in radix `2^51`;
- the `2^255 = 19 (mod p)` fold;
- ordinary carry preservation;
- the exact row-major 25-product accumulator trace;
- every low/high accumulator prefix, `COMBINE_HIGH`, and `×19` no-wrap bound;
- folded-limb, carry, and composable-u52 bounds;
- the more general unsigned weak-carry theorem from arbitrary u64 limbs to
  reusable u52 limbs.

The same source-linked layer now covers the three linear r51 leaves:

- exact add, biased subtract, and biased negate source schedules;
- assembly constants equal to the radix limbs of `4p`;
- subtraction and negation cannot underflow under the u52 input contract;
- every raw intermediate fits in u64;
- the shared parallel carry preserves each operation modulo `p`; and
- every result returns to the composable-u52 contract.

The second completed source-level target is the x8 selector transpose:

- ISA-level models of the YMM `VPUNPCKLQDQ`, `VPUNPCKHQDQ`, and
  `VSHUFI64X2` operations used by the assembly;
- a generic theorem that the eight-instruction network is exactly a 4×4
  transpose;
- two-half x8 theorems for all projective and affine coordinates; and
- explicit treatment of the affine mask-zeroed fourth qword.

The scalar-reduction foundation now also machine-checks:

- the exact six-constant radix-`2^21` fold identity modulo the group order;
- ordinary carry decomposition and the residual range `[0, 2^21)`;
- centered carry decomposition and the residual range
  `[-2^20, 2^20)`; and
- exact represented-integer preservation when a carry moves to the adjacent
  coefficient.

[`VerificationSpine.lean`](NaryaFormal/VerificationSpine.lean) states the
conditional scalar and x8 capstone theorems. It fixes the shared proof shape:
full-group integer scalar action, original bytes in the challenge hash, an
`iff` acceptance statement, and one SIMD lane-projection hypothesis. The
theorem's leaf hypotheses are open obligations rather than claims that the
current native verifier is already fully refined. See the
[refinement-spine document](../../docs/proofs/REFINEMENT_SPINE.md).

[`Radix51.lean`](NaryaFormal/Radix51.lean) contains the representation-level
algebra. [`GeneratedR51MulTrace.lean`](NaryaFormal/GeneratedR51MulTrace.lean)
is mechanically extracted from the multiply assembly source and supplies its
row-major `MUL_PAIR` order, register routing, fold, normalization, and output
mapping to [`AssemblyTrace.lean`](NaryaFormal/AssemblyTrace.lean). Its main theorem,
`radix51_mul_assembly_trace_correct`, proves the modular product and reusable
u52 output contract from only the real source precondition: every input limb
is below `2^52`. The prior abstract folded-schedule hypothesis is discharged.

[`GeneratedR51LinearTrace.lean`](NaryaFormal/GeneratedR51LinearTrace.lean) is
likewise extracted from the exact add/subtract/negate leaves. It validates
their opcodes, operands, constants, normalize call, source consumption, and
output mapping. [`LinearTrace.lean`](NaryaFormal/LinearTrace.lean) proves the
three modular operations, unsigned safety, and reusable-u52 results from the
same input contract.

[`Transpose.lean`](NaryaFormal/Transpose.lean) contains the generic lane
theorems. `tools/check_transpose_schedule.py` binds those semantics to the
actual assembly source's macros, pointer map, five limb rows, and output
offsets. See the
[transpose certificate](../../docs/proofs/TRANSPOSE_LANE_MAP.md) for the exact
claim and trust boundary.

[`ScalarReduction.lean`](NaryaFormal/ScalarReduction.lean) contains the fold
and relational carry theorems. The assembly-source checker supplies all 389
per-instruction signed intervals. The full schedule/canonical-range theorem
and binary refinement remain open; see the
[scalar-reduction contract](../../docs/proofs/SCALAR_REDUCTION_CONTRACT.md).

The r51 multiply now has a fail-closed assembly-source-to-Lean link; see the
[source refinement certificate](../../docs/proofs/R51_SOURCE_TRACE_REFINEMENT.md).
The exact canonical linked symbol is also connected to that source trace by a
restricted, fail-closed decoder. The decoded 94-instruction arithmetic core is
now executed in the fault-aware `BitVec 64` semantics and refined, in an
arbitrary selected lane, to the independently generated radix-51 result. The
output-store suffix is now separately refined: all five decoded stores require
explicit writable permissions, preserve registers and permissions, do not
cross-contaminate rows, and write the selected lane's proved limbs to the
correct SysV output rows without modifying bytes outside them. The remaining
gap is input-load composition, scratch-register semantic noninterference,
whole-program frame composition, return/ABI refinement, dispatch, and
downstream deployment identity. The Lean
result is not a verified decoder for arbitrary machine code.
The intended restricted, final-byte-linked construction is specified in the
[x86 object-refinement plan](../../docs/proofs/X86_OBJECT_REFINEMENT_PLAN.md).
Its first artifact layer is now present:
[`GeneratedR51ObjectBytes.lean`](NaryaFormal/GeneratedR51ObjectBytes.lean)
contains the exact 800-byte multiplier symbol and resolved read-only constants
from a deterministic linked ELF, while
[`ObjectBytes.lean`](NaryaFormal/ObjectBytes.lean) kernel-checks their extents,
byte ranges, and constant values. No instruction decoding or execution claim
is made by that artifact alone. [`X86Decoder.lean`](NaryaFormal/X86Decoder.lean)
accepts only the EVEX/VEX/RET forms used by the leaf, while
[`GeneratedR51InstructionTrace.lean`](NaryaFormal/GeneratedR51InstructionTrace.lean)
is independently expanded from assembly source.
[`X86ObjectRefinement.lean`](NaryaFormal/X86ObjectRefinement.lean) proves by
kernel reduction that the exact 800 bytes decode to that 129-instruction list.

[`X86Dataflow.lean`](NaryaFormal/X86Dataflow.lean) independently computes ZMM
dependencies and writes over that exact list. Starting with no caller ZMM
register assumed initialized, it kernel-checks that the load/clear/arithmetic/
store body consumes only defined values and leaves all five output registers
defined. In particular, scratch ZMM28 and ZMM30 are written before first use,
while ZMM29 and ZMM31 are never dependencies. This is a definite-assignment
certificate, not yet the semantic noninterference theorem that will remove
those arbitrary entry values from the load-to-core refinement.

[`X86VectorSemantics.lean`](NaryaFormal/X86VectorSemantics.lean) defines the
exact lane-local `BitVec 64` meaning of the vector arithmetic subset used by
that symbol, together with no-wrap refinements into unbounded naturals.
[`X86Machine.lean`](NaryaFormal/X86Machine.lean) adds byte-addressed
little-endian memory, explicit read/write permissions, 512-bit load/store
layout, the architectural `VZEROUPPER` effect on registers 0--15, and the
stack read, stack advance, and control transfer performed by `RET`. Its
permission-sensitive transitions fail closed. These are reusable semantics
and local lemmas; the checked 800 bytes have been decoded, and its arithmetic
core is proved in the BitVec machine, but the complete load-to-return machine
trace is not yet a single exported theorem.

[`X86Execution.lean`](NaryaFormal/X86Execution.lean) gives every decoded
instruction a fault-aware machine-state transition and rejects a return with
trailing decoded instructions. [`X86NatShadow.lean`](NaryaFormal/X86NatShadow.lean)
defines the paired unbounded-natural interpreter for one SIMD lane. Its phase
theorems execute the exact decoded 129-instruction program from loads through
normal return and prove that the five stored limbs equal the independently
generated 25-product arithmetic trace.
[`X86Refinement.lean`](NaryaFormal/X86Refinement.lean) proves local
machine-to-shadow refinements for XOR, AND, add, multiply, shifts, and both
IFMA halves; every u52 and no-wrap premise is explicit. Its compositional
machine runner now proves the complete 94-instruction decoded arithmetic core
lane-by-lane under the public u52 input contract. That theorem covers product,
combine, fold, and normalize, reads the fold and mask through an explicit
readable-memory contract, and proves the register-only core preserves memory.
The exact decoded
program also kernel-checks that all ten source loads precede every output
store, that the five store offsets/registers are exact, and that the epilogue
is `VZEROUPPER; RET`. [`X86MemoryRefinement.lean`](NaryaFormal/X86MemoryRefinement.lean)
closes the five-store row-content and isolation theorem from the post-arithmetic
lane relation, including its exact byte-write frame. Composing input loads,
semantic scratch independence, the whole-program frame, return behavior, and
the System V postcondition remains open.

The representation lemmas and most of the multiplication trace can be reused
by another radix-`2^51`, u52-input implementation. Such reuse still requires
an explicit mapping from that implementation's ordered operations to the
checked scalar trace. A symmetry-reduced square, canonical reducer, lazy
linear operation, or fused point formula is a different trace and is not
covered merely because it uses the same limb representation.

## Reproduce

The project pins Lean and the complete resolved dependency graph. From this
directory, verify the committed project without changing that graph:

```sh
lake build
```

`lake-manifest.json` is committed after dependency resolution. `.lake/` is a
local build/cache directory and is ignored. `lake update` is intentionally not
part of the verification procedure: it is used only for an explicit dependency
update whose manifest diff receives separate review.
