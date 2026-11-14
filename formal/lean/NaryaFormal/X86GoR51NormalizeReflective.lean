/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Leaf theorem for the production Go build of the r51 x8 product normalizer.

`ifmaNormalizeProductUncheckedX8` is the Go assembly function that carries a
vector of five folded radix-2^51 coefficients, each below `2^61`, into the
redundant u52 form every IFMA multiply consumes. This file decodes its exact
Go-linked bytes in the Lean kernel, runs the reflective IFMA checker on the
decoded body, and states the leaf theorem under the Go ABI0 contract.

The only leaf-specific reasoning is `outputs_are_normalized`: the five
expressions the checker computed are `Radix51.normalized` of the input.
-/

import NaryaFormal.X86GoR51MulReflective
import NaryaFormal.GeneratedGoR51NormalizeObjectBytes

namespace NaryaFormal.IfmaSym.GoR51Normalize

open NaryaFormal.X86
open NaryaFormal.Radix51
open NaryaFormal.IfmaSym.GoR51Mul (StackLoad decodeStackLoad execStackLoad
  runPrelude runGoSymbol)
open NaryaFormal.IfmaSym.R51Mul (outputLimbs leafPost_output_at)

/-! ### The decoded production symbol -/

def preludeBytes : Nat := 10


/-- Decode the whole Go symbol: two stack-argument loads followed by a vector
program that must end in `RET` at the last symbol byte. -/
def decodeGoSymbol (symbolAddress : Nat) (bytes : List Nat) :
    Option (List StackLoad × List Instruction) := do
  let first ← decodeStackLoad bytes 0
  let second ← decodeStackLoad bytes 5
  let program ←
    decodeProgram (symbolAddress + preludeBytes) (bytes.drop preludeBytes)
  some ([first, second], program)


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- Constructor form of the decoder's result on the committed bytes, tied to
the decoder by the kernel-checked `symbol_decodes` below. -/
def decoded : List StackLoad × List Instruction :=
  reduced% ((decodeGoSymbol GoR51NormalizeObject.symbolAddress
    GoR51NormalizeObject.symbolBytes).getD ([], []))

def prelude : List StackLoad := decoded.1

def program : List Instruction := decoded.2

def body : List Instruction := program.take 27


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The exact 197 Go-linked bytes decode completely, to `decoded`. -/
theorem symbol_decodes :
    decodeGoSymbol GoR51NormalizeObject.symbolAddress
        GoR51NormalizeObject.symbolBytes = some (prelude, program) := by
  show decodeGoSymbol GoR51NormalizeObject.symbolAddress
    GoR51NormalizeObject.symbolBytes = some decoded
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The prelude loads `out` and `x` from the two ABI0 argument slots, and the
vector program is 27 body instructions followed by `VZEROUPPER; RET`. -/
theorem decoded_shape :
    GoR51NormalizeObject.symbolBytes.length = GoR51NormalizeObject.symbolSize ∧
    prelude = [⟨.rdi, 8⟩, ⟨.rcx, 16⟩] ∧
    program = body ++ epilogue ∧ program.length = 29 := by
  decide


/-- The linked read-only constants hold 19 and `2^51 - 1`. -/
theorem linked_constants :
    GoR51NormalizeObject.ifmaFold19Bytes = [19, 0, 0, 0, 0, 0, 0, 0] ∧
    GoR51NormalizeObject.ifmaLimbMask51Bytes =
      [255, 255, 255, 255, 255, 255, 7, 0] := by
  decide


/-! ### Checker run on the decoded body -/

/-- Go ABI0 contract data after the prelude: five coefficient rows through
RCX, each selected-lane value at most `2^61 - 1`, the output object through
RDI, and the two Go-linked constants. -/
def spec : LeafSpec :=
  { inputs := [
      ⟨.rcx, 0, 2 ^ 61 - 1⟩, ⟨.rcx, 64, 2 ^ 61 - 1⟩, ⟨.rcx, 128, 2 ^ 61 - 1⟩,
      ⟨.rcx, 192, 2 ^ 61 - 1⟩, ⟨.rcx, 256, 2 ^ 61 - 1⟩]
    constants := [
      ⟨GoR51NormalizeObject.ifmaFold19Address, 19⟩,
      ⟨GoR51NormalizeObject.ifmaLimbMask51Address, 2 ^ 51 - 1⟩]
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
/-- Interval analysis alone: limb zero is below `2^51 + 19 * 1024` and every
other limb is below `2^51 + 1024`. -/
theorem output_bounds :
    (outputDefined final 0 = true ∧ outputBound final 0 < 2 ^ 51 + 19 * 1024) ∧
    (outputDefined final 64 = true ∧ outputBound final 64 < 2 ^ 51 + 1024) ∧
    (outputDefined final 128 = true ∧ outputBound final 128 < 2 ^ 51 + 1024) ∧
    (outputDefined final 192 = true ∧ outputBound final 192 < 2 ^ 51 + 1024) ∧
    (outputDefined final 256 = true ∧ outputBound final 256 < 2 ^ 51 + 1024) := by
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


/-- The five coefficient rows read through `base`, as a loose element. -/
def inputLoose (inputs : Gpr → Nat → Nat) (base : Gpr) : Loose5 :=
  ⟨inputs base 0, inputs base 64, inputs base 128, inputs base 192,
    inputs base 256⟩


/-- Normalizer-specific step: the expressions computed by the checker are the
parallel carry `Radix51.normalized` of the input. The top coefficient bound is
what makes the low-52-bit IFMA product `19 * carry` exact. -/
theorem outputs_are_normalized (inputs : Gpr → Nat → Nat)
    (htop : inputs .rcx 256 ≤ 2 ^ 61 - 1) :
    (⟨(outputExpr final 0).eval inputs, (outputExpr final 64).eval inputs,
      (outputExpr final 128).eval inputs, (outputExpr final 192).eval inputs,
      (outputExpr final 256).eval inputs⟩ : Loose5) =
      normalized (inputLoose inputs .rcx) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := output_exprs
  rw [h0, h1, h2, h3, h4]
  have hcarry : inputs .rcx 256 / 2 ^ 51 < 2 ^ 10 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  have hexact : 19 * (inputs .rcx 256 / 2 ^ 51) % 2 ^ 52 =
      19 * (inputs .rcx 256 / 2 ^ 51) :=
    Nat.mod_eq_of_lt (by omega)
  simp only [out0, out1, out2, out3, out4, Expr.eval, normalized, inputLoose,
    remainder, carry, B, hexact]


/-! ### Go ABI0 leaf theorem -/

variable {Other : Type}

/-- The two pointer arguments of `func(out *LimbsX8, x *IFMAProductX8)` as the
caller left them on the stack: `out` at `8(SP)`, `x` at `16(SP)`. -/
def argOut (entry : MachineState Other) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsp) 8)

def argX (entry : MachineState Other) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsp) 16)


/-- Machine state after the argument prelude: memory and every other register
are unchanged, and RDI, RCX hold `out`, `x`. -/
def bodyEntry (entry : MachineState Other) : MachineState Other :=
  { entry with
    gpr := setGpr (setGpr entry.gpr .rdi (argOut entry)) .rcx (argX entry) }


theorem bodyEntry_registers (entry : MachineState Other) :
    (bodyEntry entry).mem = entry.mem ∧
    (bodyEntry entry).gpr .rsp = entry.gpr .rsp ∧
    (bodyEntry entry).gpr .rdi = argOut entry ∧
    (bodyEntry entry).gpr .rcx = argX entry := by
  simp [bodyEntry, setGpr]


theorem run_prelude (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true) :
    runPrelude prelude entry = .ok (bodyEntry entry) := by
  have h8 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 16 0 8 harguments (by omega)
  have h16 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 16) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 16 8 8 harguments (by omega)
  rw [decoded_shape.2.1]
  simp [runPrelude, execStackLoad, setGpr, h8, h16, bodyEntry, argOut, argX]


/-- Shared core for the reference and relocated layouts. -/
theorem go_leaf_core (leafSpec : LeafSpec) (vectorBody : List Instruction)
    (hinputs : leafSpec.inputs = spec.inputs)
    (hbase : leafSpec.outputBase = Gpr.rdi)
    (haccepts : runSym leafSpec vectorBody initialSymState = some final)
    (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true)
    (hpre : LeafPre leafSpec lane (bodyEntry entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput leafSpec (bodyEntry entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude (vectorBody ++ epilogue) entry =
        .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry entry) returned =
        normalized (inputLoose (entryInputs lane (bodyEntry entry)) .rcx) ∧
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        looseValue (inputLoose (entryInputs lane (bodyEntry entry)) .rcx) % P ∧
      (outputLimbs lane (bodyEntry entry) returned).l0 < 2 ^ 51 + 19 * 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l1 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l2 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l3 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l4 < 2 ^ 51 + 1024 ∧
      LeafPost leafSpec lane final (bodyEntry entry) returned := by
  obtain ⟨hmem, hrsp, -, -⟩ := bodyEntry_registers entry
  have hreturnBody : readableBytes (bodyEntry entry).mem
      ((bodyEntry entry).gpr .rsp) 8 = true := by
    rw [hmem, hrsp]
    exact hreturn
  have hstackBody : ∀ offset, offset < 8 →
      OutsideOutput leafSpec (bodyEntry entry)
        (addressAdd ((bodyEntry entry).gpr .rsp) offset) := by
    intro offset hoffset
    rw [hrsp]
    exact hstack offset hoffset
  obtain ⟨returned, hrun, hpost⟩ :=
    run_leaf leafSpec lane (bodyEntry entry) hpre vectorBody final haccepts
      hreturnBody hstackBody
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := output_bounds
  obtain ⟨hv0, hl0⟩ := leafPost_output_at hpost 0 hb0.1
  obtain ⟨hv1, hl1⟩ := leafPost_output_at hpost 64 hb1.1
  obtain ⟨hv2, hl2⟩ := leafPost_output_at hpost 128 hb2.1
  obtain ⟨hv3, hl3⟩ := leafPost_output_at hpost 192 hb3.1
  obtain ⟨hv4, hl4⟩ := leafPost_output_at hpost 256 hb4.1
  rw [hbase] at hv0 hv1 hv2 hv3 hv4
  have htop : entryInputs lane (bodyEntry entry) .rcx 256 ≤ 2 ^ 61 - 1 :=
    hpre.inputBound ⟨.rcx, 256, 2 ^ 61 - 1⟩ (by rw [hinputs]; decide)
  have hrows : outputLimbs lane (bodyEntry entry) returned =
      ⟨(outputExpr final 0).eval (entryInputs lane (bodyEntry entry)),
        (outputExpr final 64).eval (entryInputs lane (bodyEntry entry)),
        (outputExpr final 128).eval (entryInputs lane (bodyEntry entry)),
        (outputExpr final 192).eval (entryInputs lane (bodyEntry entry)),
        (outputExpr final 256).eval (entryInputs lane (bodyEntry entry))⟩ := by
    simp only [outputLimbs, Loose5.mk.injEq]
    exact ⟨hv0, hv1, hv2, hv3, hv4⟩
  have hlimbs := hrows.trans
    (outputs_are_normalized (entryInputs lane (bodyEntry entry)) htop)
  have hprogram : runGoSymbol prelude (vectorBody ++ epilogue) entry =
      .ok (.returned returned) := by
    unfold runGoSymbol
    rw [run_prelude entry harguments]
    exact hrun
  refine ⟨returned, hprogram, hlimbs, ?_, ?_, ?_, ?_, ?_, ?_, hpost⟩
  · rw [hlimbs]
    exact parallel_carry_preserves_mod _
  · exact lt_of_eq_of_lt hv0 (lt_of_le_of_lt hl0 hb0.2)
  · exact lt_of_eq_of_lt hv1 (lt_of_le_of_lt hl1 hb1.2)
  · exact lt_of_eq_of_lt hv2 (lt_of_le_of_lt hl2 hb2.2)
  · exact lt_of_eq_of_lt hv3 (lt_of_le_of_lt hl3 hb3.2)
  · exact lt_of_eq_of_lt hv4 (lt_of_le_of_lt hl4 hb4.2)


/-- Leaf theorem for the production Go-linked product normalizer bytes.

The committed 197 symbol bytes decode to a two-instruction argument prelude and
a 29-instruction vector program. From any entry state in which

* the two ABI0 argument slots at `8(SP)..23(SP)` are readable,
* `LeafPre spec lane` holds after the prelude: the five 64-byte coefficient
  rows of `x` are readable with selected-lane values at most `2^61 - 1`, the
  two linked constants are readable with values 19 and `2^51 - 1`, and the
  320-byte output object is writable,
* the return slot at `0(SP)` is readable and does not overlap the output,

the symbol returns normally; the selected lane of the output is the parallel
carry of the selected-lane input, hence represents the same value modulo
`2^255 - 19`; limb zero is below `2^51 + 19 * 1024` and every other limb is
below `2^51 + 1024`; and `LeafPost` holds relative to the post-prelude state.

`x` and `out` may overlap arbitrarily, and the argument slots may overlap the
output, because every argument and input load precedes the first store. -/
theorem go_r51_normalize_refines (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true)
    (hpre : LeafPre spec lane (bodyEntry entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput spec (bodyEntry entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    decodeGoSymbol GoR51NormalizeObject.symbolAddress
        GoR51NormalizeObject.symbolBytes = some (prelude, program) ∧
    ∃ returned,
      runGoSymbol prelude program entry = .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry entry) returned =
        normalized (inputLoose (entryInputs lane (bodyEntry entry)) .rcx) ∧
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        looseValue (inputLoose (entryInputs lane (bodyEntry entry)) .rcx) % P ∧
      (outputLimbs lane (bodyEntry entry) returned).l0 < 2 ^ 51 + 19 * 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l1 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l2 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l3 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l4 < 2 ^ 51 + 1024 ∧
      LeafPost spec lane final (bodyEntry entry) returned := by
  refine ⟨symbol_decodes, ?_⟩
  rw [decoded_shape.2.2.1]
  exact go_leaf_core spec body rfl rfl checker_accepts lane entry harguments
    hpre hreturn hstack


/-! ### Any link layout -/

/-- Rename the reference constant addresses to those of another link. -/
def relocation (fold19 mask51 : Nat) : Nat → Nat := fun address =>
  if address = GoR51NormalizeObject.ifmaFold19Address then fold19
  else if address = GoR51NormalizeObject.ifmaLimbMask51Address then mask51
  else address


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body reads exactly the two declared constants, each once. -/
theorem body_broadcast_addresses :
    broadcastAddresses body =
      [GoR51NormalizeObject.ifmaLimbMask51Address,
        GoR51NormalizeObject.ifmaFold19Address] := by
  decide


theorem relocation_faithful (fold19 mask51 : Nat) (hdistinct : fold19 ≠ mask51) :
    RenameFaithful (relocation fold19 mask51) spec (broadcastAddresses body) := by
  rw [body_broadcast_addresses]
  intro constant hmember address haddress hequal
  simp only [spec, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hmember haddress
  rcases hmember with rfl | rfl <;> rcases haddress with rfl | rfl <;>
    simp_all [relocation, GoR51NormalizeObject.ifmaFold19Address,
      GoR51NormalizeObject.ifmaLimbMask51Address]


/-- The normalizer leaf theorem for any link layout: for arbitrary distinct
constant addresses, the same prelude and the same vector program with its two
broadcast addresses renamed satisfy the same statement. -/
theorem go_r51_normalize_refines_relocated (fold19 mask51 : Nat)
    (hdistinct : fold19 ≠ mask51) (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true)
    (hpre : LeafPre (relocateSpec (relocation fold19 mask51) spec) lane
      (bodyEntry entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput (relocateSpec (relocation fold19 mask51) spec)
        (bodyEntry entry) (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude
          (program.map (relocateInstruction (relocation fold19 mask51))) entry =
        .ok (.returned returned) ∧
      outputLimbs lane (bodyEntry entry) returned =
        normalized (inputLoose (entryInputs lane (bodyEntry entry)) .rcx) ∧
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        looseValue (inputLoose (entryInputs lane (bodyEntry entry)) .rcx) % P ∧
      (outputLimbs lane (bodyEntry entry) returned).l0 < 2 ^ 51 + 19 * 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l1 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l2 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l3 < 2 ^ 51 + 1024 ∧
      (outputLimbs lane (bodyEntry entry) returned).l4 < 2 ^ 51 + 1024 ∧
      LeafPost (relocateSpec (relocation fold19 mask51) spec) lane final
        (bodyEntry entry) returned := by
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


/-! ### Contract margin and a fail-closed check -/

/-- The same contract with every coefficient bound widened to `2^64 - 1`. -/
def u64Spec : LeafSpec :=
  { spec with
    inputs := spec.inputs.map fun row => { row with bound := 2 ^ 64 - 1 } }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The `2^61` input bound is not load-bearing for exactness: the checker also
accepts the body for arbitrary 64-bit coefficients, and every stored limb is
still below `2^52`. The `2^61` contract only buys the tighter output bounds. -/
theorem u64_inputs_accepted :
    (runSym u64Spec body initialSymState).isSome = true ∧
    ∀ displacement ∈ [0, 64, 128, 192, 256],
      outputBound ((runSym u64Spec body initialSymState).getD initialSymState)
        displacement < 2 ^ 52 := by
  decide


/-- A fold constant that is not a valid 52-bit IFMA operand. -/
def wideFoldSpec : LeafSpec :=
  { spec with
    constants := [
      ⟨GoR51NormalizeObject.ifmaFold19Address, 2 ^ 52⟩,
      ⟨GoR51NormalizeObject.ifmaLimbMask51Address, 2 ^ 51 - 1⟩] }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body is rejected if the fold constant could reach `2^52`, where the
IFMA multiply would silently drop its top bits. -/
theorem wide_fold_constant_rejected :
    (runSym wideFoldSpec body initialSymState).isSome = false := by
  decide


/-! ### Non-vacuity -/

/-- Memory used only to show the Go leaf contract is satisfiable. -/
def witnessMemory : Memory :=
  { byte := fun address =>
      if address = BitVec.ofNat 64 GoR51NormalizeObject.ifmaFold19Address then
        BitVec.ofNat 8 19
      else if address =
          BitVec.ofNat 64 (GoR51NormalizeObject.ifmaLimbMask51Address + 6) then
        BitVec.ofNat 8 7
      else if BitVec.ofNat 64 GoR51NormalizeObject.ifmaLimbMask51Address ≤ address ∧
          address <
            BitVec.ofNat 64 (GoR51NormalizeObject.ifmaLimbMask51Address + 6) then
        BitVec.ofNat 8 255
      else BitVec.ofNat 8 0
    perm := fun _ => ⟨true, true, false⟩ }


/-- Both pointer arguments are zero and the stack pointer is `2^21`. -/
def witnessEntry : MachineState Unit :=
  { gpr := fun register =>
      if register = .rsp then BitVec.ofNat 64 (2 ^ 21) else BitVec.ofNat 64 0
    zmm := fun _ _ => BitVec.ofNat 64 0
    opmask := fun _ => BitVec.ofNat 64 0
    rflags := BitVec.ofNat 64 0
    mxcsr := BitVec.ofNat 32 0
    mem := witnessMemory
    rip := BitVec.ofNat 64 0
    other := () }


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_facts :
    (bodyEntry witnessEntry).gpr .rdi = BitVec.ofNat 64 0 ∧
    (∀ row ∈ spec.inputs,
      entryInputs 0 (bodyEntry witnessEntry) row.base row.displacement ≤
        row.bound) ∧
    (∀ constant ∈ spec.constants,
      (constant.address < 2 ^ 64 ∧ constant.value < 2 ^ 64) ∧
      loadQwordLE (bodyEntry witnessEntry).mem
          (BitVec.ofNat 64 constant.address) =
        BitVec.ofNat 64 constant.value) := by
  decide


/-- The hypotheses of `go_r51_normalize_refines` are jointly satisfiable for
lane zero. -/
theorem leaf_contract_satisfiable :
    readableBytes witnessEntry.mem
        (addressAdd (witnessEntry.gpr .rsp) 8) 16 = true ∧
      LeafPre spec 0 (bodyEntry witnessEntry) ∧
      readableBytes witnessEntry.mem (witnessEntry.gpr .rsp) 8 = true ∧
      ∀ offset, offset < 8 →
        OutsideOutput spec (bodyEntry witnessEntry)
          (addressAdd (witnessEntry.gpr .rsp) offset) := by
  obtain ⟨hrdi, hinputs, hconstants⟩ := witness_facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [readableBytes, witnessEntry, witnessMemory]
  · exact
      { outputBound := by decide
        inputReadable := by
          intro row _
          simp [readableBytes, bodyEntry, witnessEntry, witnessMemory]
        inputBound := hinputs
        constantRange := fun constant hmember => (hconstants constant hmember).1
        constantReadable := by
          intro constant _
          simp [readableBytes, bodyEntry, witnessEntry, witnessMemory]
        constantValue := fun constant hmember => (hconstants constant hmember).2
        outputWritable := by
          simp [writableBytes, bodyEntry, witnessEntry, witnessMemory] }
  · simp [readableBytes, witnessEntry, witnessMemory]
  · intro offset hoffset inner hinner
    have hinner' : inner < 320 := hinner
    have hbase : (bodyEntry witnessEntry).gpr spec.outputBase =
        BitVec.ofNat 64 0 := hrdi
    have hrsp : witnessEntry.gpr .rsp = BitVec.ofNat 64 (2 ^ 21) := rfl
    rw [hbase, hrsp]
    exact addressAdd_ofNat_ne (2 ^ 21) 0 offset inner (by omega) (by omega)
      (by omega)

end NaryaFormal.IfmaSym.GoR51Normalize
