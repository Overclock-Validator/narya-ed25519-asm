/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Leaf theorem for the production Go build of the r51 x8 negator.

`ifmaNegateNormalizedUncheckedX8` computes `4p - x` limb by limb, with `4p`
supplied as two bias constants and `x` read directly from memory, and applies
one parallel carry.
This file decodes its exact Go-linked bytes in the Lean kernel, runs the
reflective IFMA checker on the decoded body, and states the leaf theorem under
the Go ABI0 contract. The subtraction is accepted only because the checker can
read off the syntax that the minuend is at least the bias, which is at least
the subtrahend's bound: no borrow is possible.
-/

import NaryaFormal.X86GoLeaf
import NaryaFormal.GeneratedGoR51NegateObjectBytes

namespace NaryaFormal.IfmaSym.GoR51Negate

open NaryaFormal.X86
open NaryaFormal.Radix51
open NaryaFormal.IfmaSym.GoR51Mul (StackLoad runGoSymbol)
open NaryaFormal.IfmaSym.R51Mul (outputLimbs)
open NaryaFormal.IfmaSym.GoLeaf

/-! ### The decoded production symbol -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- Constructor form of the decoder's result on the committed bytes, tied to
the decoder by the kernel-checked `symbol_decodes` below. -/
def decoded : List StackLoad × List Instruction :=
  reduced% ((decodeGoSymbol 2 GoR51NegateObject.symbolAddress
    GoR51NegateObject.symbolBytes).getD ([], []))

def prelude : List StackLoad := decoded.1

def program : List Instruction := decoded.2

def body : List Instruction := program.take 32


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The exact 235 Go-linked bytes decode completely, to `decoded`. -/
theorem symbol_decodes :
    decodeGoSymbol 2 GoR51NegateObject.symbolAddress
        GoR51NegateObject.symbolBytes = some (prelude, program) := by
  show decodeGoSymbol 2 GoR51NegateObject.symbolAddress
    GoR51NegateObject.symbolBytes = some decoded
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The prelude loads the 2 ABI0 pointer arguments, and the vector program
is 32 body instructions followed by `VZEROUPPER; RET`. -/
theorem decoded_shape :
    GoR51NegateObject.symbolBytes.length = GoR51NegateObject.symbolSize ∧
    prelude = prelude2 ∧
    program = body ++ epilogue ∧ program.length = 32 + 2 := by
  decide


/-- Limb-zero subtraction bias, `4 * (2^51 - 19)`. -/
def bias0 : Nat := 9007199254740916

/-- Subtraction bias of limbs one to four, `4 * (2^51 - 1)`. -/
def biasN : Nat := 9007199254740988


/-- The biases are four times the prime, limb by limb, and the linked
read-only constants hold them, 19, and `2^51 - 1`. -/
theorem linked_constants :
    bias0 = 4 * (2 ^ 51 - 19) ∧ biasN = 4 * (2 ^ 51 - 1) ∧
    GoR51NegateObject.ifmaSubBias0Bytes = [180, 255, 255, 255, 255, 255, 31, 0] ∧
    GoR51NegateObject.ifmaSubBiasNBytes = [252, 255, 255, 255, 255, 255, 31, 0] ∧
    GoR51NegateObject.ifmaFold19Bytes = [19, 0, 0, 0, 0, 0, 0, 0] ∧
    GoR51NegateObject.ifmaLimbMask51Bytes =
      [255, 255, 255, 255, 255, 255, 7, 0] := by
  decide


theorem bias_value :
    looseValue ⟨bias0, biasN, biasN, biasN, biasN⟩ = 4 * P := by
  norm_num [looseValue, bias0, biasN, B, P]


/-! ### Checker run on the decoded body -/

/-- Go ABI0 contract data after the prelude. -/
def spec : LeafSpec :=
  { inputs := u52Rows .rcx
    constants := [
      ⟨GoR51NegateObject.ifmaSubBias0Address, bias0⟩,
      ⟨GoR51NegateObject.ifmaSubBiasNAddress, biasN⟩,
      ⟨GoR51NegateObject.ifmaFold19Address, 19⟩,
      ⟨GoR51NegateObject.ifmaLimbMask51Address, 2 ^ 51 - 1⟩]
    outputBase := .rdi
    outputBytes := 320 }


def final : SymState :=
  (runSym spec body initialSymState).getD initialSymState


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The checker accepts every decoded body instruction. -/
theorem checker_accepts : runSym spec body initialSymState = some final := by
  apply eq_some_getD_of_isSome
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem outputs_defined :
    outputDefined final 0 = true ∧ outputDefined final 64 = true ∧
    outputDefined final 128 = true ∧ outputDefined final 192 = true ∧
    outputDefined final 256 = true := by
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Interval analysis alone. -/
theorem output_bounds :
    outputBound final 0 < 2 ^ 51 + 19 * 4 ∧
    outputBound final 64 < 2 ^ 51 + 4 ∧
    outputBound final 128 < 2 ^ 51 + 4 ∧
    outputBound final 192 < 2 ^ 51 + 4 ∧
    outputBound final 256 < 2 ^ 51 + 4 := by
  decide


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


/-- Limbwise biased negation `4p - x`. -/
def negLoose (x : Loose5) : Loose5 :=
  ⟨bias0 - x.l0, biasN - x.l1, biasN - x.l2, biasN - x.l3, biasN - x.l4⟩


/-- With `x` in u52 form no limb subtraction truncates, so the biased negation
plus `x` is four times the prime. -/
theorem negLoose_value (x : Loose5)
    (hx : x.l0 ≤ 2 ^ 52 - 1 ∧ x.l1 ≤ 2 ^ 52 - 1 ∧ x.l2 ≤ 2 ^ 52 - 1 ∧
      x.l3 ≤ 2 ^ 52 - 1 ∧ x.l4 ≤ 2 ^ 52 - 1) :
    looseValue (negLoose x) + looseValue x = 4 * P := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hx
  rw [← bias_value]
  simp only [looseValue, negLoose, bias0, biasN, B] at *
  norm_num at *
  omega


/-- Negator-specific step: the expressions computed by the checker are the
parallel carry of the biased negation. -/
theorem outputs_are_normalized_negation (inputs : Gpr → Nat → Nat) :
    outputValues final inputs = normalized (negLoose (inputLoose inputs .rcx)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := output_exprs
  unfold outputValues
  rw [h0, h1, h2, h3, h4]
  have hcarry : (9007199254740988 - inputs .rcx 256) / 2 ^ 51 < 2 ^ 10 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  have hexact :
      19 * ((9007199254740988 - inputs .rcx 256) / 2 ^ 51) % 2 ^ 52 =
        19 * ((9007199254740988 - inputs .rcx 256) / 2 ^ 51) :=
    Nat.mod_eq_of_lt (by omega)
  simp only [out0, out1, out2, out3, out4, Expr.eval, normalized, negLoose,
    inputLoose, remainder, carry, B, bias0, biasN, hexact]


/-! ### Go ABI0 leaf theorem -/

variable {Other : Type}

/-- Shared core for the reference and relocated layouts. -/
theorem go_leaf_core (leafSpec : LeafSpec) (vectorBody : List Instruction)
    (hinputs : leafSpec.inputs = spec.inputs)
    (hbase : leafSpec.outputBase = Gpr.rdi)
    (haccepts : runSym leafSpec vectorBody initialSymState = some final)
    (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true)
    (hpre : LeafPre leafSpec lane (bodyEntry2 entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput leafSpec (bodyEntry2 entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude2 (vectorBody ++ epilogue) entry =
        .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry2 entry) returned =
        normalized (negLoose
          (inputLoose (entryInputs lane (bodyEntry2 entry)) .rcx)) ∧
      (looseValue (outputLimbs lane (bodyEntry2 entry) returned) +
          looseValue (inputLoose (entryInputs lane (bodyEntry2 entry)) .rcx)) % P =
        0 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l0 < 2 ^ 51 + 19 * 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l1 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l2 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l3 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l4 < 2 ^ 51 + 4 ∧
      LeafPost leafSpec lane final (bodyEntry2 entry) returned := by
  obtain ⟨hmem, hrsp, -⟩ := bodyEntry2_frame entry
  obtain ⟨returned, hrun, hpost⟩ :=
    go_leaf_run leafSpec prelude2 vectorBody final haccepts lane entry
      (bodyEntry2 entry) (run_prelude2 entry harguments) hmem hrsp hpre
      hreturn hstack
  obtain ⟨hrows, hl0, hl1, hl2, hl3, hl4⟩ :=
    output_rows leafSpec final hbase outputs_defined lane (bodyEntry2 entry)
      returned hpost
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := output_bounds
  have hx := input_u52 leafSpec lane (bodyEntry2 entry) hpre .rcx
    (by rw [hinputs]; intro row hrow; exact hrow)
  have hlimbs := hrows.trans
    (outputs_are_normalized_negation (entryInputs lane (bodyEntry2 entry)))
  refine ⟨returned, hrun, hlimbs, ?_, lt_of_le_of_lt hl0 hb0,
    lt_of_le_of_lt hl1 hb1, lt_of_le_of_lt hl2 hb2, lt_of_le_of_lt hl3 hb3,
    lt_of_le_of_lt hl4 hb4, hpost⟩
  rw [hlimbs, Nat.add_mod, parallel_carry_preserves_mod, ← Nat.add_mod,
    negLoose_value _ hx, Nat.mul_mod_left]


/-- Leaf theorem for the production Go-linked negator bytes.

From any entry state in which the two ABI0 argument slots are readable,
`LeafPre spec lane` holds after the prelude (the five 64-byte rows of `x`
readable with selected-lane values at most `2^52 - 1`, the four linked
constants readable with their values, the 320-byte output writable), and the
return slot is readable and outside the output, the symbol returns normally;
the selected lane of the output is the parallel carry of `4p - x`, so
`out + x` represents zero modulo `2^255 - 19`; limb zero is below `2^51 + 76`
and every other limb is below `2^51 + 4`; and `LeafPost` holds.

`x` and `out` may overlap arbitrarily. -/
theorem go_r51_negate_refines (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true)
    (hpre : LeafPre spec lane (bodyEntry2 entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput spec (bodyEntry2 entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    decodeGoSymbol 2 GoR51NegateObject.symbolAddress
        GoR51NegateObject.symbolBytes = some (prelude2, program) ∧
    ∃ returned,
      runGoSymbol prelude2 program entry = .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry2 entry) returned =
        normalized (negLoose
          (inputLoose (entryInputs lane (bodyEntry2 entry)) .rcx)) ∧
      (looseValue (outputLimbs lane (bodyEntry2 entry) returned) +
          looseValue (inputLoose (entryInputs lane (bodyEntry2 entry)) .rcx)) % P =
        0 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l0 < 2 ^ 51 + 19 * 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l1 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l2 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l3 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l4 < 2 ^ 51 + 4 ∧
      LeafPost spec lane final (bodyEntry2 entry) returned := by
  refine ⟨?_, ?_⟩
  · rw [← decoded_shape.2.1]
    exact symbol_decodes
  · rw [decoded_shape.2.2.1]
    exact go_leaf_core spec body rfl rfl checker_accepts lane entry harguments
      hpre hreturn hstack


/-! ### Any link layout -/

/-- Rename the reference constant addresses to those of another link. -/
def relocation (sub0 subN fold19 mask51 : Nat) : Nat → Nat := fun address =>
  if address = GoR51NegateObject.ifmaSubBias0Address then sub0
  else if address = GoR51NegateObject.ifmaSubBiasNAddress then subN
  else if address = GoR51NegateObject.ifmaFold19Address then fold19
  else if address = GoR51NegateObject.ifmaLimbMask51Address then mask51
  else address


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body reads exactly the four declared constants, each once. -/
theorem body_broadcast_addresses :
    broadcastAddresses body =
      [GoR51NegateObject.ifmaSubBias0Address,
        GoR51NegateObject.ifmaSubBiasNAddress,
        GoR51NegateObject.ifmaLimbMask51Address,
        GoR51NegateObject.ifmaFold19Address] := by
  decide


theorem relocation_faithful (sub0 subN fold19 mask51 : Nat)
    (hdistinct : [sub0, subN, fold19, mask51].Nodup) :
    RenameFaithful (relocation sub0 subN fold19 mask51) spec
      (broadcastAddresses body) := by
  rw [body_broadcast_addresses]
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hdistinct
  intro constant hmember address haddress hequal
  simp only [spec, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hmember haddress
  rcases hmember with rfl | rfl | rfl | rfl <;>
    rcases haddress with rfl | rfl | rfl | rfl <;>
    simp_all [relocation, GoR51NegateObject.ifmaSubBias0Address,
      GoR51NegateObject.ifmaSubBiasNAddress,
      GoR51NegateObject.ifmaFold19Address,
      GoR51NegateObject.ifmaLimbMask51Address]


/-- The leaf theorem for any link layout with four distinct constant
addresses. -/
theorem go_r51_negate_refines_relocated (sub0 subN fold19 mask51 : Nat)
    (hdistinct : [sub0, subN, fold19, mask51].Nodup) (lane : Fin 8)
    (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true)
    (hpre : LeafPre (relocateSpec (relocation sub0 subN fold19 mask51) spec)
      lane (bodyEntry2 entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput (relocateSpec (relocation sub0 subN fold19 mask51) spec)
        (bodyEntry2 entry) (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude2
          (program.map
            (relocateInstruction (relocation sub0 subN fold19 mask51))) entry =
        .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry2 entry) returned =
        normalized (negLoose
          (inputLoose (entryInputs lane (bodyEntry2 entry)) .rcx)) ∧
      (looseValue (outputLimbs lane (bodyEntry2 entry) returned) +
          looseValue (inputLoose (entryInputs lane (bodyEntry2 entry)) .rcx)) % P =
        0 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l0 < 2 ^ 51 + 19 * 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l1 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l2 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l3 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry2 entry) returned).l4 < 2 ^ 51 + 4 ∧
      LeafPost (relocateSpec (relocation sub0 subN fold19 mask51) spec) lane
        final (bodyEntry2 entry) returned := by
  have haccepts :
      runSym (relocateSpec (relocation sub0 subN fold19 mask51) spec)
        (body.map (relocateInstruction (relocation sub0 subN fold19 mask51)))
        initialSymState = some final := by
    rw [runSym_relocate _ _ _ _
      (relocation_faithful sub0 subN fold19 mask51 hdistinct)]
    exact checker_accepts
  have hsplit :
      program.map (relocateInstruction (relocation sub0 subN fold19 mask51)) =
        body.map (relocateInstruction (relocation sub0 subN fold19 mask51)) ++
          epilogue := by
    rw [decoded_shape.2.2.1, List.map_append]
    rfl
  rw [hsplit]
  exact go_leaf_core (relocateSpec (relocation sub0 subN fold19 mask51) spec) _
    rfl rfl haccepts lane entry harguments hpre hreturn hstack


/-! ### Fail-closed check -/

/-- The same contract with `x` only known to be below `2^54`. -/
def wideSpec : LeafSpec :=
  { spec with
    inputs := (u52Rows .rcx).map fun row => { row with bound := 2 ^ 54 - 1 } }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body is rejected if the subtrahend could exceed the bias: the 64-bit
subtraction could then borrow. -/
theorem unbounded_subtrahend_rejected :
    (runSym wideSpec body initialSymState).isSome = false := by
  decide


/-! ### Non-vacuity -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_facts :
    (bodyEntry2 (witnessEntry spec.constants)).gpr .rdi =
      BitVec.ofNat 64 0 ∧
    (∀ row ∈ spec.inputs,
      entryInputs 0 (bodyEntry2 (witnessEntry spec.constants)) row.base
        row.displacement ≤ row.bound) ∧
    (∀ constant ∈ spec.constants,
      (constant.address < 2 ^ 64 ∧ constant.value < 2 ^ 64) ∧
      loadQwordLE (bodyEntry2 (witnessEntry spec.constants)).mem
          (BitVec.ofNat 64 constant.address) =
        BitVec.ofNat 64 constant.value) := by
  decide


/-- The hypotheses of `go_r51_negate_refines` are jointly satisfiable for
lane zero. -/
theorem leaf_contract_satisfiable :
    readableBytes (witnessEntry spec.constants).mem
        (addressAdd ((witnessEntry spec.constants).gpr .rsp) 8)
        16 = true ∧
      LeafPre spec 0 (bodyEntry2 (witnessEntry spec.constants)) ∧
      readableBytes (witnessEntry spec.constants).mem
        ((witnessEntry spec.constants).gpr .rsp) 8 = true ∧
      ∀ offset, offset < 8 →
        OutsideOutput spec (bodyEntry2 (witnessEntry spec.constants))
          (addressAdd ((witnessEntry spec.constants).gpr .rsp) offset) :=
  witness_contract spec 16 (bodyEntry2 (witnessEntry spec.constants))
    rfl witness_facts.1 (by decide) witness_facts.2.1 witness_facts.2.2

end NaryaFormal.IfmaSym.GoR51Negate
