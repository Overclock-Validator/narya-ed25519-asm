/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Leaf theorem for the production Go build of the r51 x8 adder.

`ifmaAddNormalizedUncheckedX8` adds two u52 field elements limb by limb, with
the second operand read directly from memory, and applies one parallel carry.
This file decodes its exact Go-linked bytes in the Lean kernel, runs the
reflective IFMA checker on the decoded body, and states the leaf theorem under
the Go ABI0 contract.
-/

import NaryaFormal.X86GoLeaf
import NaryaFormal.GeneratedGoR51AddObjectBytes

namespace NaryaFormal.IfmaSym.GoR51Add

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
  reduced% ((decodeGoSymbol 3 GoR51AddObject.symbolAddress
    GoR51AddObject.symbolBytes).getD ([], []))

def prelude : List StackLoad := decoded.1

def program : List Instruction := decoded.2

def body : List Instruction := program.take 32


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The exact 236 Go-linked bytes decode completely, to `decoded`. -/
theorem symbol_decodes :
    decodeGoSymbol 3 GoR51AddObject.symbolAddress GoR51AddObject.symbolBytes =
      some (prelude, program) := by
  show decodeGoSymbol 3 GoR51AddObject.symbolAddress
    GoR51AddObject.symbolBytes = some decoded
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The prelude loads `out`, `x`, `y` from the three ABI0 argument slots, and
the vector program is 32 body instructions followed by `VZEROUPPER; RET`. -/
theorem decoded_shape :
    GoR51AddObject.symbolBytes.length = GoR51AddObject.symbolSize ∧
    prelude = prelude3 ∧
    program = body ++ epilogue ∧ program.length = 34 := by
  decide


/-- The linked read-only constants hold 19 and `2^51 - 1`. -/
theorem linked_constants :
    GoR51AddObject.ifmaFold19Bytes = [19, 0, 0, 0, 0, 0, 0, 0] ∧
    GoR51AddObject.ifmaLimbMask51Bytes =
      [255, 255, 255, 255, 255, 255, 7, 0] := by
  decide


/-! ### Checker run on the decoded body -/

/-- Go ABI0 contract data after the prelude: u52 rows of `x` through RCX and
of `y` through RBX, the output object through RDI, and the two constants. -/
def spec : LeafSpec :=
  { inputs := u52Rows .rcx ++ u52Rows .rbx
    constants := [
      ⟨GoR51AddObject.ifmaFold19Address, 19⟩,
      ⟨GoR51AddObject.ifmaLimbMask51Address, 2 ^ 51 - 1⟩]
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
/-- Interval analysis alone: the carry out of a sum of two u52 limbs is at
most three. -/
theorem output_bounds :
    outputBound final 0 < 2 ^ 51 + 19 * 4 ∧ outputBound final 64 < 2 ^ 51 + 4 ∧
    outputBound final 128 < 2 ^ 51 + 4 ∧ outputBound final 192 < 2 ^ 51 + 4 ∧
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


/-- Limbwise sum of two loose elements. -/
def addLoose (x y : Loose5) : Loose5 :=
  ⟨x.l0 + y.l0, x.l1 + y.l1, x.l2 + y.l2, x.l3 + y.l3, x.l4 + y.l4⟩


theorem addLoose_value (x y : Loose5) :
    looseValue (addLoose x y) = looseValue x + looseValue y := by
  simp only [looseValue, addLoose]
  ring


/-- Adder-specific step: the expressions computed by the checker are the
parallel carry of the limbwise sum. The top-limb bounds make the low-52-bit
IFMA product `19 * carry` exact. -/
theorem outputs_are_normalized_sum (inputs : Gpr → Nat → Nat)
    (hx : inputs .rcx 256 ≤ 2 ^ 52 - 1) (hy : inputs .rbx 256 ≤ 2 ^ 52 - 1) :
    outputValues final inputs =
      normalized (addLoose (inputLoose inputs .rcx) (inputLoose inputs .rbx)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := output_exprs
  unfold outputValues
  rw [h0, h1, h2, h3, h4]
  have hcarry : (inputs .rcx 256 + inputs .rbx 256) / 2 ^ 51 < 2 ^ 10 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  have hexact : 19 * ((inputs .rcx 256 + inputs .rbx 256) / 2 ^ 51) % 2 ^ 52 =
      19 * ((inputs .rcx 256 + inputs .rbx 256) / 2 ^ 51) :=
    Nat.mod_eq_of_lt (by omega)
  simp only [out0, out1, out2, out3, out4, Expr.eval, normalized, addLoose,
    inputLoose, remainder, carry, B, hexact]


/-! ### Go ABI0 leaf theorem -/

variable {Other : Type}

/-- Shared core for the reference and relocated layouts. -/
theorem go_leaf_core (leafSpec : LeafSpec) (vectorBody : List Instruction)
    (hinputs : leafSpec.inputs = spec.inputs)
    (hbase : leafSpec.outputBase = Gpr.rdi)
    (haccepts : runSym leafSpec vectorBody initialSymState = some final)
    (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true)
    (hpre : LeafPre leafSpec lane (bodyEntry3 entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput leafSpec (bodyEntry3 entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude3 (vectorBody ++ epilogue) entry =
        .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry3 entry) returned =
        normalized (addLoose
          (inputLoose (entryInputs lane (bodyEntry3 entry)) .rcx)
          (inputLoose (entryInputs lane (bodyEntry3 entry)) .rbx)) ∧
      looseValue (outputLimbs lane (bodyEntry3 entry) returned) % P =
        (looseValue (inputLoose (entryInputs lane (bodyEntry3 entry)) .rcx) +
          looseValue (inputLoose (entryInputs lane (bodyEntry3 entry)) .rbx)) % P ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l0 < 2 ^ 51 + 19 * 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l1 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l2 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l3 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l4 < 2 ^ 51 + 4 ∧
      LeafPost leafSpec lane final (bodyEntry3 entry) returned := by
  obtain ⟨hmem, hrsp, -, -, -⟩ := bodyEntry3_frame entry
  obtain ⟨returned, hrun, hpost⟩ :=
    go_leaf_run leafSpec prelude3 vectorBody final haccepts lane entry
      (bodyEntry3 entry) (run_prelude3 entry harguments) hmem hrsp hpre hreturn
      hstack
  obtain ⟨hrows, hl0, hl1, hl2, hl3, hl4⟩ :=
    output_rows leafSpec final hbase outputs_defined lane (bodyEntry3 entry)
      returned hpost
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := output_bounds
  have hx := input_u52 leafSpec lane (bodyEntry3 entry) hpre .rcx
    (by rw [hinputs]; intro row hrow; exact List.mem_append_left _ hrow)
  have hy := input_u52 leafSpec lane (bodyEntry3 entry) hpre .rbx
    (by rw [hinputs]; intro row hrow; exact List.mem_append_right _ hrow)
  have hlimbs := hrows.trans
    (outputs_are_normalized_sum (entryInputs lane (bodyEntry3 entry))
      hx.2.2.2.2 hy.2.2.2.2)
  refine ⟨returned, hrun, hlimbs, ?_, lt_of_le_of_lt hl0 hb0,
    lt_of_le_of_lt hl1 hb1, lt_of_le_of_lt hl2 hb2, lt_of_le_of_lt hl3 hb3,
    lt_of_le_of_lt hl4 hb4, hpost⟩
  rw [hlimbs, parallel_carry_preserves_mod, addLoose_value]


/-- Leaf theorem for the production Go-linked adder bytes.

The committed 236 symbol bytes decode to the three-argument prelude and a
34-instruction vector program. From any entry state in which

* the three ABI0 argument slots at `8(SP)..31(SP)` are readable,
* `LeafPre spec lane` holds after the prelude: the ten 64-byte rows of `x` and
  `y` are readable with selected-lane values at most `2^52 - 1`, the two linked
  constants are readable with values 19 and `2^51 - 1`, and the 320-byte output
  object is writable,
* the return slot at `0(SP)` is readable and does not overlap the output,

the symbol returns normally; the selected lane of the output is the parallel
carry of the limbwise sum, hence represents `x + y` modulo `2^255 - 19`; limb
zero is below `2^51 + 76` and every other limb is below `2^51 + 4`; and
`LeafPost` holds relative to the post-prelude state.

`x`, `y`, and `out` may overlap arbitrarily, because every load, including the
memory operands of the additions, precedes the first store. -/
theorem go_r51_add_refines (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true)
    (hpre : LeafPre spec lane (bodyEntry3 entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput spec (bodyEntry3 entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    decodeGoSymbol 3 GoR51AddObject.symbolAddress GoR51AddObject.symbolBytes =
        some (prelude3, program) ∧
    ∃ returned,
      runGoSymbol prelude3 program entry = .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry3 entry) returned =
        normalized (addLoose
          (inputLoose (entryInputs lane (bodyEntry3 entry)) .rcx)
          (inputLoose (entryInputs lane (bodyEntry3 entry)) .rbx)) ∧
      looseValue (outputLimbs lane (bodyEntry3 entry) returned) % P =
        (looseValue (inputLoose (entryInputs lane (bodyEntry3 entry)) .rcx) +
          looseValue (inputLoose (entryInputs lane (bodyEntry3 entry)) .rbx)) % P ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l0 < 2 ^ 51 + 19 * 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l1 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l2 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l3 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l4 < 2 ^ 51 + 4 ∧
      LeafPost spec lane final (bodyEntry3 entry) returned := by
  refine ⟨?_, ?_⟩
  · rw [← decoded_shape.2.1]
    exact symbol_decodes
  · rw [decoded_shape.2.2.1]
    exact go_leaf_core spec body rfl rfl checker_accepts lane entry harguments
      hpre hreturn hstack


/-! ### Any link layout -/

/-- Rename the reference constant addresses to those of another link. -/
def relocation (fold19 mask51 : Nat) : Nat → Nat := fun address =>
  if address = GoR51AddObject.ifmaFold19Address then fold19
  else if address = GoR51AddObject.ifmaLimbMask51Address then mask51
  else address


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body reads exactly the two declared constants, each once. -/
theorem body_broadcast_addresses :
    broadcastAddresses body =
      [GoR51AddObject.ifmaLimbMask51Address,
        GoR51AddObject.ifmaFold19Address] := by
  decide


theorem relocation_faithful (fold19 mask51 : Nat) (hdistinct : fold19 ≠ mask51) :
    RenameFaithful (relocation fold19 mask51) spec (broadcastAddresses body) := by
  rw [body_broadcast_addresses]
  intro constant hmember address haddress hequal
  simp only [spec, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hmember haddress
  rcases hmember with rfl | rfl <;> rcases haddress with rfl | rfl <;>
    simp_all [relocation, GoR51AddObject.ifmaFold19Address,
      GoR51AddObject.ifmaLimbMask51Address]


/-- The adder leaf theorem for any link layout. -/
theorem go_r51_add_refines_relocated (fold19 mask51 : Nat)
    (hdistinct : fold19 ≠ mask51) (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true)
    (hpre : LeafPre (relocateSpec (relocation fold19 mask51) spec) lane
      (bodyEntry3 entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput (relocateSpec (relocation fold19 mask51) spec)
        (bodyEntry3 entry) (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude3
          (program.map (relocateInstruction (relocation fold19 mask51))) entry =
        .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry3 entry) returned =
        normalized (addLoose
          (inputLoose (entryInputs lane (bodyEntry3 entry)) .rcx)
          (inputLoose (entryInputs lane (bodyEntry3 entry)) .rbx)) ∧
      looseValue (outputLimbs lane (bodyEntry3 entry) returned) % P =
        (looseValue (inputLoose (entryInputs lane (bodyEntry3 entry)) .rcx) +
          looseValue (inputLoose (entryInputs lane (bodyEntry3 entry)) .rbx)) % P ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l0 < 2 ^ 51 + 19 * 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l1 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l2 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l3 < 2 ^ 51 + 4 ∧
      (outputLimbs lane (bodyEntry3 entry) returned).l4 < 2 ^ 51 + 4 ∧
      LeafPost (relocateSpec (relocation fold19 mask51) spec) lane final
        (bodyEntry3 entry) returned := by
  have haccepts : runSym (relocateSpec (relocation fold19 mask51) spec)
      (body.map (relocateInstruction (relocation fold19 mask51)))
      initialSymState = some final := by
    rw [runSym_relocate _ _ _ _ (relocation_faithful fold19 mask51 hdistinct)]
    exact checker_accepts
  have hsplit : program.map (relocateInstruction (relocation fold19 mask51)) =
      body.map (relocateInstruction (relocation fold19 mask51)) ++ epilogue := by
    rw [decoded_shape.2.2.1, List.map_append]
    rfl
  rw [hsplit]
  exact go_leaf_core (relocateSpec (relocation fold19 mask51) spec) _ rfl rfl
    haccepts lane entry harguments hpre hreturn hstack


/-! ### Fail-closed check -/

/-- The same contract with `y` only known to be below `2^64`. -/
def wideSpec : LeafSpec :=
  { spec with
    inputs := u52Rows .rcx ++
      (u52Rows .rbx).map fun row => { row with bound := 2 ^ 64 - 1 } }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body is rejected if the memory operand could make the 64-bit addition
wrap. -/
theorem unbounded_memory_operand_rejected :
    (runSym wideSpec body initialSymState).isSome = false := by
  decide


/-! ### Non-vacuity -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_facts :
    (bodyEntry3 (witnessEntry spec.constants)).gpr .rdi = BitVec.ofNat 64 0 ∧
    (∀ row ∈ spec.inputs,
      entryInputs 0 (bodyEntry3 (witnessEntry spec.constants)) row.base
        row.displacement ≤ row.bound) ∧
    (∀ constant ∈ spec.constants,
      (constant.address < 2 ^ 64 ∧ constant.value < 2 ^ 64) ∧
      loadQwordLE (bodyEntry3 (witnessEntry spec.constants)).mem
          (BitVec.ofNat 64 constant.address) =
        BitVec.ofNat 64 constant.value) := by
  decide


/-- The hypotheses of `go_r51_add_refines` are jointly satisfiable for lane
zero. -/
theorem leaf_contract_satisfiable :
    readableBytes (witnessEntry spec.constants).mem
        (addressAdd ((witnessEntry spec.constants).gpr .rsp) 8) 24 = true ∧
      LeafPre spec 0 (bodyEntry3 (witnessEntry spec.constants)) ∧
      readableBytes (witnessEntry spec.constants).mem
        ((witnessEntry spec.constants).gpr .rsp) 8 = true ∧
      ∀ offset, offset < 8 →
        OutsideOutput spec (bodyEntry3 (witnessEntry spec.constants))
          (addressAdd ((witnessEntry spec.constants).gpr .rsp) offset) :=
  witness_contract spec 24 (bodyEntry3 (witnessEntry spec.constants)) rfl
    witness_facts.1 (by decide) witness_facts.2.1 witness_facts.2.2

end NaryaFormal.IfmaSym.GoR51Add
