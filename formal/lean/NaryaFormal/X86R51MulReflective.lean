/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Reflective re-derivation of the r51 IFMA multiplier leaf theorem.

The checker in `X86IfmaSymbolic.lean` is run by kernel evaluation on the exact
decoded multiplier body. Its generic soundness theorem then yields the machine,
memory, wraparound, and System V facts. The only multiplier-specific reasoning
is `r51_mul_outputs_are_assembly_output`: the five checker expressions equal
the generated scalar trace, whose field correctness is the existing
`radix51_mul_assembly_trace_correct`.

This file does not import the hand-composed phase proofs
(`X86NatShadow` through `X86EpilogueRefinement`). It is an independent route to
the same leaf statement.
-/

import NaryaFormal.X86IfmaSoundness
import NaryaFormal.AssemblyTrace

namespace NaryaFormal.IfmaSym.R51Mul

open NaryaFormal.X86
open NaryaFormal.X86.GeneratedR51InstructionTrace
open NaryaFormal.Radix51
open NaryaFormal.Radix51.GeneratedR51MulTrace

/-- Leaf contract data: ten readable 64-byte input rows whose selected lane is
at most `2^52 - 1`, the two linked constants, and a 320-byte output object. -/
def spec : LeafSpec :=
  { inputs := [
      ⟨.rsi, 0, 2 ^ 52 - 1⟩, ⟨.rsi, 64, 2 ^ 52 - 1⟩, ⟨.rsi, 128, 2 ^ 52 - 1⟩,
      ⟨.rsi, 192, 2 ^ 52 - 1⟩, ⟨.rsi, 256, 2 ^ 52 - 1⟩,
      ⟨.rdx, 0, 2 ^ 52 - 1⟩, ⟨.rdx, 64, 2 ^ 52 - 1⟩, ⟨.rdx, 128, 2 ^ 52 - 1⟩,
      ⟨.rdx, 192, 2 ^ 52 - 1⟩, ⟨.rdx, 256, 2 ^ 52 - 1⟩]
    constants := [
      ⟨R51Object.ifma_fold19Address, 19⟩,
      ⟨R51Object.ifma_mask51Address, 2 ^ 51 - 1⟩]
    outputBase := .rdi
    outputBytes := 320 }


def body : List Instruction :=
  loadPhase ++ clearPhase ++ arithmeticCorePhase ++ storePhase


set_option maxRecDepth 4096 in
theorem expected_program_split : expectedProgram = body ++ epilogue := by
  decide


def final : SymState :=
  (runSym spec body initialSymState).getD initialSymState


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The checker accepts all 127 non-returning instructions: every load is a
declared input row, every arithmetic step is free of 64-bit wraparound, every
IFMA operand fits in 52 bits, and every store lands in the output object. -/
theorem checker_accepts : runSym spec body initialSymState = some final := by
  apply eq_some_getD_of_isSome
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Interval analysis alone shows all five stored limbs are below `2^52`. -/
theorem output_bounds :
    (outputDefined final 0 = true ∧ outputBound final 0 < 2 ^ 52) ∧
    (outputDefined final 64 = true ∧ outputBound final 64 < 2 ^ 52) ∧
    (outputDefined final 128 = true ∧ outputBound final 128 < 2 ^ 52) ∧
    (outputDefined final 192 = true ∧ outputBound final 192 < 2 ^ 52) ∧
    (outputDefined final 256 = true ∧ outputBound final 256 < 2 ^ 52) := by
  decide


/-! ### Checker expressions equal the generated scalar trace -/

def out0 : Expr := reduced% (outputExpr final 0)
def out1 : Expr := reduced% (outputExpr final 64)
def out2 : Expr := reduced% (outputExpr final 128)
def out3 : Expr := reduced% (outputExpr final 192)
def out4 : Expr := reduced% (outputExpr final 256)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem output_exprs :
    outputExpr final 0 = out0 ∧ outputExpr final 64 = out1 ∧
    outputExpr final 128 = out2 ∧ outputExpr final 192 = out3 ∧
    outputExpr final 256 = out4 := by
  decide


/-- The five input limbs of one operand, read from the declared rows. -/
def inputLimbs (inputs : Gpr → Nat → Nat) (base : Gpr) : FiveLimbs :=
  fun limb =>
    match limb.val with
    | 0 => inputs base 0
    | 1 => inputs base 64
    | 2 => inputs base 128
    | 3 => inputs base 192
    | _ => inputs base 256


theorem inputLimbs_apply (inputs : Gpr → Nat → Nat) (base : Gpr) :
    inputLimbs inputs base 0 = inputs base 0 ∧
    inputLimbs inputs base 1 = inputs base 64 ∧
    inputLimbs inputs base 2 = inputs base 128 ∧
    inputLimbs inputs base 3 = inputs base 192 ∧
    inputLimbs inputs base 4 = inputs base 256 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


/-- Multiplier-specific step: the expressions computed by the checker are the
generated scalar multiplication trace. Proved by ring normalisation under the
quotient and remainder operators; no bounds are involved. -/
theorem outputs_are_assembly_output (inputs : Gpr → Nat → Nat) :
    (⟨(outputExpr final 0).eval inputs, (outputExpr final 64).eval inputs,
      (outputExpr final 128).eval inputs, (outputExpr final 192).eval inputs,
      (outputExpr final 256).eval inputs⟩ : Loose5) =
      assemblyOutput (inputLimbs inputs .rsi) (inputLimbs inputs .rdx) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := output_exprs
  obtain ⟨x0, x1, x2, x3, x4⟩ := inputLimbs_apply inputs .rsi
  obtain ⟨y0, y1, y2, y3, y4⟩ := inputLimbs_apply inputs .rdx
  rw [h0, h1, h2, h3, h4]
  simp only [assemblyOutput, traceRemainder, traceCarry, lowTerms, highTerms,
    List.sum_cons, List.sum_nil, lo52, hi52, foldConstant, Radix51.U52,
    x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, Loose5.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [out0, Expr.eval]
    ring_nf
  · simp only [out1, Expr.eval]
    ring_nf
  · simp only [out2, Expr.eval]
    ring_nf
  · simp only [out3, Expr.eval]
    ring_nf
  · simp only [out4, Expr.eval]
    ring_nf


/-! ### Whole-leaf theorem -/

variable {Other : Type}

/-- Selected-lane limbs of the five output rows of a machine state. -/
def outputLimbs (lane : Fin 8) (entry state : MachineState Other) : Loose5 :=
  { l0 := (loadZmm state.mem (addressAdd (entry.gpr .rdi) 0) lane).toNat
    l1 := (loadZmm state.mem (addressAdd (entry.gpr .rdi) 64) lane).toNat
    l2 := (loadZmm state.mem (addressAdd (entry.gpr .rdi) 128) lane).toNat
    l3 := (loadZmm state.mem (addressAdd (entry.gpr .rdi) 192) lane).toNat
    l4 := (loadZmm state.mem (addressAdd (entry.gpr .rdi) 256) lane).toNat }


theorem leafPost_output_at {spec : LeafSpec} {lane : Fin 8}
    {bodyFinal : SymState} {entry state : MachineState Other}
    (hpost : LeafPost spec lane bodyFinal entry state) (displacement : Nat)
    (hdefined : outputDefined bodyFinal displacement = true) :
    (loadZmm state.mem
        (addressAdd (entry.gpr spec.outputBase) displacement) lane).toNat =
      (outputExpr bodyFinal displacement).eval (entryInputs lane entry) ∧
    (outputExpr bodyFinal displacement).eval (entryInputs lane entry) ≤
      outputBound bodyFinal displacement := by
  unfold outputDefined at hdefined
  unfold outputExpr outputBound
  cases hvalue : bodyFinal.output displacement with
  | none => simp [hvalue] at hdefined
  | some value => exact hpost.output displacement value hvalue


/-- The leaf contract bounds every selected-lane input limb below `2^52`. -/
theorem input_limbs_u52 (lane : Fin 8) (entry : MachineState Other)
    (hpre : LeafPre spec lane entry) (base : Gpr)
    (h0 : (⟨base, 0, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs)
    (h1 : (⟨base, 64, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs)
    (h2 : (⟨base, 128, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs)
    (h3 : (⟨base, 192, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs)
    (h4 : (⟨base, 256, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs) :
    AssemblyTrace.LimbsU52 (inputLimbs (entryInputs lane entry) base) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := inputLimbs_apply (entryInputs lane entry) base
  have hrow (displacement : Nat)
      (hmember : (⟨base, displacement, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs) :
      entryInputs lane entry base displacement < Radix51.U52 := by
    have hle := hpre.inputBound ⟨base, displacement, 2 ^ 52 - 1⟩ hmember
    have hle' : entryInputs lane entry base displacement ≤ 2 ^ 52 - 1 := hle
    unfold Radix51.U52
    omega
  intro limb
  fin_cases limb
  · show inputLimbs (entryInputs lane entry) base 0 < Radix51.U52
    rw [a0]
    exact hrow 0 h0
  · show inputLimbs (entryInputs lane entry) base 1 < Radix51.U52
    rw [a1]
    exact hrow 64 h1
  · show inputLimbs (entryInputs lane entry) base 2 < Radix51.U52
    rw [a2]
    exact hrow 128 h2
  · show inputLimbs (entryInputs lane entry) base 3 < Radix51.U52
    rw [a3]
    exact hrow 192 h3
  · show inputLimbs (entryInputs lane entry) base 4 < Radix51.U52
    rw [a4]
    exact hrow 256 h4


/-- Under `LeafPost`, the five stored rows are the generated scalar trace of
the two entry-memory inputs, and each stored limb is below `2^52` by the
checker's interval analysis. -/
theorem output_limbs_of_post (lane : Fin 8) (entry returned : MachineState Other)
    (hpost : LeafPost spec lane final entry returned) :
    outputLimbs lane entry returned =
        assemblyOutput (inputLimbs (entryInputs lane entry) .rsi)
          (inputLimbs (entryInputs lane entry) .rdx) ∧
      (outputLimbs lane entry returned).l0 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l1 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l2 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l3 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l4 < 2 ^ 52 := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := output_bounds
  obtain ⟨hv0, hl0⟩ := leafPost_output_at hpost 0 hb0.1
  obtain ⟨hv1, hl1⟩ := leafPost_output_at hpost 64 hb1.1
  obtain ⟨hv2, hl2⟩ := leafPost_output_at hpost 128 hb2.1
  obtain ⟨hv3, hl3⟩ := leafPost_output_at hpost 192 hb3.1
  obtain ⟨hv4, hl4⟩ := leafPost_output_at hpost 256 hb4.1
  have hrows : outputLimbs lane entry returned =
      ⟨(outputExpr final 0).eval (entryInputs lane entry),
        (outputExpr final 64).eval (entryInputs lane entry),
        (outputExpr final 128).eval (entryInputs lane entry),
        (outputExpr final 192).eval (entryInputs lane entry),
        (outputExpr final 256).eval (entryInputs lane entry)⟩ := by
    simp only [outputLimbs, Loose5.mk.injEq]
    exact ⟨hv0, hv1, hv2, hv3, hv4⟩
  refine ⟨hrows.trans (outputs_are_assembly_output (entryInputs lane entry)),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_eq_of_lt hv0 (lt_of_le_of_lt hl0 hb0.2)
  · exact lt_of_eq_of_lt hv1 (lt_of_le_of_lt hl1 hb1.2)
  · exact lt_of_eq_of_lt hv2 (lt_of_le_of_lt hl2 hb2.2)
  · exact lt_of_eq_of_lt hv3 (lt_of_le_of_lt hl3 hb3.2)
  · exact lt_of_eq_of_lt hv4 (lt_of_le_of_lt hl4 hb4.2)


/-- Whole-leaf machine theorem for the r51 multiplier, obtained reflectively.

The committed 800-byte symbol decodes to `expectedProgram`. From any entry
state satisfying `LeafPre spec lane`, with a readable return slot that does not
overlap the 320-byte output object, the program returns normally and:

* the selected lane of the five output rows represents the product of the two
  selected-lane inputs modulo `2^255 - 19`;
* each output limb is below `2^52`;
* `LeafPost` holds: no byte outside the output object changes, permissions are
  unchanged, RSP advances by eight, RIP is the entry return word, and every
  other GPR, RFLAGS, MXCSR, and unmodeled state are preserved.

Input rows may overlap the output object arbitrarily. -/
theorem r51_multiplier_reflective (lane : Fin 8) (entry : MachineState Other)
    (hpre : LeafPre spec lane entry)
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput spec entry (addressAdd (entry.gpr .rsp) offset)) :
    decodeProgram R51Object.symbolAddress R51Object.symbolBytes =
        some expectedProgram ∧
    ∃ returned,
      runProgram expectedProgram entry = .ok (.returned returned) ∧
      looseValue (outputLimbs lane entry returned) % P =
        (radixValue (inputLimbs (entryInputs lane entry) .rsi) *
          radixValue (inputLimbs (entryInputs lane entry) .rdx)) % P ∧
      (outputLimbs lane entry returned).l0 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l1 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l2 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l3 < 2 ^ 52 ∧
      (outputLimbs lane entry returned).l4 < 2 ^ 52 ∧
      LeafPost spec lane final entry returned := by
  obtain ⟨returned, hrun, hpost⟩ :=
    run_leaf spec lane entry hpre body final checker_accepts hreturn hstack
  obtain ⟨hlimbs, h0, h1, h2, h3, h4⟩ :=
    output_limbs_of_post lane entry returned hpost
  have htrace := AssemblyTrace.radix51_mul_assembly_trace_correct
    (inputLimbs (entryInputs lane entry) .rsi)
    (inputLimbs (entryInputs lane entry) .rdx)
    (input_limbs_u52 lane entry hpre .rsi (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (input_limbs_u52 lane entry hpre .rdx (by decide) (by decide) (by decide)
      (by decide) (by decide))
  have hvalue : looseValue (outputLimbs lane entry returned) % P =
      (radixValue (inputLimbs (entryInputs lane entry) .rsi) *
        radixValue (inputLimbs (entryInputs lane entry) .rdx)) % P := by
    rw [hlimbs]
    exact htrace.1
  have hprogram : runProgram expectedProgram entry = .ok (.returned returned) := by
    rw [expected_program_split]
    exact hrun
  exact ⟨r51_object_decodes_to_source_instruction_trace, returned, hprogram,
    hvalue, h0, h1, h2, h3, h4, hpost⟩


/-! ### Non-vacuity -/

/-- Memory used only to show the leaf contract is satisfiable: every byte is
readable and writable, the two linked constants hold their values, and every
other byte is zero. -/
def witnessMemory : Memory :=
  { byte := fun address =>
      if address = BitVec.ofNat 64 R51Object.ifma_fold19Address then
        BitVec.ofNat 8 19
      else if address = BitVec.ofNat 64 (R51Object.ifma_mask51Address + 6) then
        BitVec.ofNat 8 7
      else if BitVec.ofNat 64 R51Object.ifma_mask51Address ≤ address ∧
          address < BitVec.ofNat 64 (R51Object.ifma_mask51Address + 6) then
        BitVec.ofNat 8 255
      else BitVec.ofNat 8 0
    perm := fun _ => ⟨true, true, false⟩ }


/-- Both operands at address zero, the output object at `2^20`, and the return
slot at `2^21`. -/
def witnessEntry : MachineState Unit :=
  { gpr := fun register =>
      if register = .rdi then BitVec.ofNat 64 (2 ^ 20)
      else if register = .rsp then BitVec.ofNat 64 (2 ^ 21)
      else BitVec.ofNat 64 0
    zmm := fun _ _ => BitVec.ofNat 64 0
    opmask := fun _ => BitVec.ofNat 64 0
    rflags := BitVec.ofNat 64 0
    mxcsr := BitVec.ofNat 32 0
    mem := witnessMemory
    rip := BitVec.ofNat 64 0
    other := () }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_inputs :
    ∀ row ∈ spec.inputs,
      entryInputs 0 witnessEntry row.base row.displacement ≤ row.bound := by
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_constants :
    ∀ constant ∈ spec.constants,
      (constant.address < 2 ^ 64 ∧ constant.value < 2 ^ 64) ∧
      loadQwordLE witnessEntry.mem (BitVec.ofNat 64 constant.address) =
        BitVec.ofNat 64 constant.value := by
  decide


/-- The hypotheses of `r51_multiplier_reflective` are jointly satisfiable for
lane zero, so the theorem does not hold vacuously. -/
theorem leaf_contract_satisfiable :
    LeafPre spec 0 witnessEntry ∧
      readableBytes witnessEntry.mem (witnessEntry.gpr .rsp) 8 = true ∧
      ∀ offset, offset < 8 →
        OutsideOutput spec witnessEntry
          (addressAdd (witnessEntry.gpr .rsp) offset) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      { outputBound := by decide
        inputReadable := by
          intro row _
          simp [readableBytes, witnessEntry, witnessMemory]
        inputBound := witness_inputs
        constantRange := fun constant hmember =>
          (witness_constants constant hmember).1
        constantReadable := by
          intro constant _
          simp [readableBytes, witnessEntry, witnessMemory]
        constantValue := fun constant hmember =>
          (witness_constants constant hmember).2
        outputWritable := by simp [writableBytes, witnessEntry, witnessMemory] }
  · simp [readableBytes, witnessEntry, witnessMemory]
  · intro offset hoffset inner hinner
    have hinner' : inner < 320 := hinner
    exact addressAdd_ofNat_ne (2 ^ 21) (2 ^ 20) offset inner (by omega) (by omega)
      (by omega)


/-! ### Fail-closed checks -/

/-- The same body is rejected if an input row is only known to be below
`2^53`: an IFMA operand could then exceed 52 bits. -/
def wideSpec : LeafSpec :=
  { spec with
    inputs := spec.inputs.map (fun row => { row with bound := 2 ^ 53 - 1 }) }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem wide_inputs_rejected :
    (runSym wideSpec body initialSymState).isSome = false := by
  decide


/-- Reading a register that was never defined is rejected. -/
theorem undefined_register_rejected :
    (runSym spec [.vpaddq 10 11 12] initialSymState).isSome = false := by
  decide


/-- Accumulating into a register that was not cleared first is rejected. -/
theorem uncleared_accumulator_rejected :
    (runSym spec
      [.vmovdqu64Load 0 .rsi 0, .vmovdqu64Load 5 .rdx 0,
       .vpmadd52luq 10 0 5] initialSymState).isSome = false := by
  decide


/-- A load after the first store is rejected, which is what permits inputs to
overlap the output object. -/
theorem load_after_store_rejected :
    (runSym spec
      [.vmovdqu64Load 0 .rsi 0, .vmovdqu64Store .rdi 0 0,
       .vmovdqu64Load 1 .rsi 64] initialSymState).isSome = false := by
  decide


/-- A load from a row that is not a declared input is rejected. -/
theorem undeclared_input_rejected :
    (runSym spec [.vmovdqu64Load 0 .rsi 320] initialSymState).isSome = false := by
  decide


/-- A store outside the 320-byte output object is rejected. -/
theorem store_outside_output_rejected :
    (runSym spec
      [.vmovdqu64Load 0 .rsi 0, .vmovdqu64Store .rdi 320 0]
      initialSymState).isSome = false := by
  decide


/-- A left shift whose tracked bound could wrap 64 bits is rejected: a value
below `2^52` shifted by 13 can reach `2^65`. -/
theorem wrapping_shift_rejected :
    (runSym spec
      [.vmovdqu64Load 0 .rsi 0, .vpsllq 1 0 13] initialSymState).isSome =
        false := by
  decide

end NaryaFormal.IfmaSym.R51Mul
