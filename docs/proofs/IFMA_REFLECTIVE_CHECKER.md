# Reflective checker for IFMA field leaves

This note describes a leaf-independent route from decoded AVX-512 IFMA
instructions to a machine-level theorem, and its first use: re-deriving the r51
multiplier leaf theorem as a known-answer test.

## Why

The original multiplier proof is hand-composed from eight phase modules
(`X86NatShadow.lean` through `X86EpilogueRefinement.lean`, about 2,800 lines).
Every one of those modules mentions the multiplier's instruction list, register
allocation, or memory layout, so none of it transfers to another leaf. The
square chain, fused doubling, fused Niels, and packed leaves would each need a
proof of similar size, and each would break when its assembly is retuned.

The reflective route proves the machine reasoning once.

## Structure

1. **Checker** (`X86IfmaSymbolic.lean`). A partial symbolic executor over the
   decoded instruction type. For one arbitrary selected lane, each defined ZMM
   register carries:

   - an exact unbounded-natural expression over the entry-memory input rows;
   - an inclusive upper bound on that expression.

   The executor returns `none` unless it can justify the step. It rejects:

   - reading an undefined register (only `vpxorq` with two identical sources,
     the zeroing idiom, defines a register from nothing);
   - `vpaddq`, `vpmullq`, `vpsllq`, or an IFMA accumulate whose tracked bounds
     admit 64-bit wraparound;
   - an IFMA multiply operand whose bound is not below `2^52`;
   - `vpandq` with anything other than a constant mask `2^bits - 1`;
   - a load from a row that is not a declared input, a broadcast from an
     address that is not a declared constant, and any load or broadcast after
     the first store;
   - a store that is not a 64-byte row, at a multiple of 64, inside the
     declared output object;
   - `VZEROUPPER` and `RET`, which belong to the epilogue.

2. **Soundness** (`X86IfmaSoundness.lean`). `executeSym_sound` proves, once per
   instruction form, that an accepted step is matched by a fault-free step of
   the byte-addressed machine model that preserves a simulation relation: each
   defined register's selected lane equals its expression evaluated on entry
   memory and is within its bound; memory is untouched before the first store;
   bytes outside the output object are untouched afterwards; stored rows read
   back their expressions. `run_leaf` composes a whole accepted body with the
   exact `VZEROUPPER; RET` suffix into a System V leaf statement (`LeafPost`).

3. **Per-leaf instance**. A leaf supplies a `LeafSpec` (input rows with
   per-row bounds, constants, output object) and then needs:

   - `decide`: the checker accepts the decoded body;
   - `decide`: the output bounds it computed are the bounds the caller needs;
   - one arithmetic lemma: the output expressions equal the intended scalar
     trace. For the multiplier this is ring normalisation under `/` and `%`.

No per-leaf proof mentions permissions, aliasing, wraparound, scratch
registers, the frame, or the return sequence.

## The multiplier instance

`X86R51MulReflective.lean` instantiates the checker on the exact decoded body
of `narya_r51x8_mul_ifma`.

- `checker_accepts`: all 127 non-returning instructions are accepted.
- `output_bounds`: interval analysis alone gives every stored limb below
  `2^52`. The computed bounds are `2^51 + 1918`, `2^51 + 532`, `2^51 + 424`,
  `2^51 + 316`, and `2^51 + 208`.
- `outputs_are_assembly_output`: the five output expressions equal
  `GeneratedR51MulTrace.assemblyOutput`.
- `r51_multiplier_reflective`: the committed symbol bytes decode to the
  program; from any entry state satisfying the leaf contract the program
  returns normally; the selected lane of the output represents the product of
  the selected-lane inputs modulo `2^255 - 19`; every output limb is below
  `2^52`; and `LeafPost` holds.
- `leaf_contract_satisfiable`: a concrete entry state meets every hypothesis.
- Seven fail-closed theorems, including `wide_inputs_rejected`: the same body
  is rejected if the inputs are only known to be below `2^53`.

The file imports `X86IfmaSoundness.lean` and the pure arithmetic theorem
`radix51_mul_assembly_trace_correct`. It does not import the hand-composed
phase modules, so it is an independent derivation of the leaf statement from
the same decoded bytes and the same machine model.

Multiplier-specific proof text is about 260 lines, plus about 180 lines of
witness and fail-closed checks. The reusable checker and soundness proof are
about 1,000 lines.

### Contract compared with `run_r51_multiplier_refines`

Same: arbitrary selected lane, ten readable input rows with selected-lane
values below `2^52`, the two linked constants readable with their values, a
writable 320-byte output, a readable return slot that does not overlap the
output, and arbitrary overlap between inputs and output.

Additional in the reflective theorem: the modular product statement and the
limb bounds are part of the conclusion, and RFLAGS, MXCSR, and unmodeled state
are shown preserved.

Not exposed by the reflective theorem: the exact final vector-register state.
`LeafPost` says nothing about ZMM registers after return, which are
caller-saved.

The original phase proof is left in place. Whether to retire it is a separate
decision.

## Limits

- Straight-line code only. A loop needs a bounds-only invariant.
- No load after the first store, so a leaf that reads back its own workspace
  is rejected.
- One output object addressed from one register.
- No subtraction. The add, subtract, and negate leaves and every fused point
  formula need `vpsubq` with a non-underflow rule.
- One selected lane. All supported instructions act lane-wise, so the theorem
  holds for every lane separately, but a half-register packed layout needs
  per-lane-group tracking.
- The decoder still covers only the multiplier symbol. Each new leaf needs its
  bytes decoded to the instruction type before the checker can run on it.
- The expression tree is not shared. A leaf with deep reuse of intermediate
  values may need a DAG representation to keep kernel evaluation fast.

## Trusted boundary

Unchanged from the multiplier proof: the Lean kernel and mathlib, the
restricted decoder and instruction semantics, the byte extraction scripts, and
the canonical proof link. The checker, the `reduced%` elaborator used to write
down expression normal forms, and the Python tooling are not trusted: every
checker result used by a theorem is established by kernel evaluation, and every
`reduced%` term is paired with a kernel-checked equation.

The capstone depends on `Lean.ofReduceBool` through the `bv_decide` proof of
`loadQwordLE_storeQwordLE_same` in `X86Machine.lean`, as the original
multiplier theorem does.
