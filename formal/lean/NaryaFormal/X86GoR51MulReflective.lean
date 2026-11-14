/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Leaf theorem for the production Go build of the r51 x8 multiplier.

The production verifier is the Go module `narya-ed25519`. Its multiplier is the
Go assembly function `ifmaMulNormalizedUncheckedX8`, assembled and linked by
the Go toolchain. Those bytes are not the bytes of this repository's GNU
assembly leaf: the calling convention, base registers, constant addresses, and
entry prelude differ.

This file decodes the exact Go-linked symbol bytes in the Lean kernel, runs the
reflective IFMA checker on the decoded body, and states the leaf theorem under
the Go ABI0 contract. No source-level transcript of the Go assembly is
consulted: the claim is about the bytes.
-/

import NaryaFormal.X86R51MulReflective
import NaryaFormal.X86IfmaRelocation
import NaryaFormal.GeneratedGoR51ObjectBytes

namespace NaryaFormal.IfmaSym.GoR51Mul

open NaryaFormal.X86
open NaryaFormal.Radix51
open NaryaFormal.Radix51.GeneratedR51MulTrace
open NaryaFormal.IfmaSym.R51Mul (inputLimbs outputLimbs)

/-! ### Go ABI0 argument prelude -/

/-- `MOVQ displacement(SP), destination`. -/
structure StackLoad where
  destination : Gpr
  displacement : Nat
  deriving DecidableEq, Repr


/-- Unextended ModRM `reg` field. RSP is not accepted as a destination. -/
def gprOfRegField : Nat → Option Gpr
  | 0 => some .rax
  | 1 => some .rcx
  | 2 => some .rdx
  | 3 => some .rbx
  | 5 => some .rbp
  | 6 => some .rsi
  | 7 => some .rdi
  | _ => none


/-- Fail-closed decoder for exactly `REX.W 8B /r` with ModRM mode 1, an SIB
byte selecting base RSP with no index, and a non-negative 8-bit displacement. -/
def decodeStackLoad (bytes : List Nat) (offset : Nat) : Option StackLoad := do
  let rex ← byteAt bytes offset
  let opcode ← byteAt bytes (offset + 1)
  let modrm ← byteAt bytes (offset + 2)
  let sib ← byteAt bytes (offset + 3)
  let displacement ← byteAt bytes (offset + 4)
  if rex ≠ 0x48 ∨ opcode ≠ 0x8b ∨ bitField modrm 6 2 ≠ 1 ∨
      bitField modrm 0 3 ≠ 4 ∨ sib ≠ 0x24 ∨ 128 ≤ displacement then none else
  let destination ← gprOfRegField (bitField modrm 3 3)
  some ⟨destination, displacement⟩


def preludeBytes : Nat := 15


/-- Decode the whole Go symbol: three stack-argument loads followed by a
vector program that must end in `RET` at the last symbol byte. -/
def decodeGoSymbol (symbolAddress : Nat) (bytes : List Nat) :
    Option (List StackLoad × List Instruction) := do
  let first ← decodeStackLoad bytes 0
  let second ← decodeStackLoad bytes 5
  let third ← decodeStackLoad bytes 10
  let program ←
    decodeProgram (symbolAddress + preludeBytes) (bytes.drop preludeBytes)
  some ([first, second, third], program)


variable {Other : Type}

def execStackLoad (state : MachineState Other) (load : StackLoad) :
    Except Fault (MachineState Other) :=
  let address := addressAdd (state.gpr .rsp) load.displacement
  if readableBytes state.mem address 8 then
    .ok { state with
      gpr := setGpr state.gpr load.destination (loadQwordLE state.mem address) }
  else
    .error (.readFault address)


def runPrelude : List StackLoad → MachineState Other →
    Except Fault (MachineState Other)
  | [], state => .ok state
  | load :: rest, state =>
      match execStackLoad state load with
      | .error fault => .error fault
      | .ok next => runPrelude rest next


/-- Execution of a decoded Go symbol from its first byte to its return. -/
def runGoSymbol (prelude : List StackLoad) (program : List Instruction)
    (state : MachineState Other) : Except Fault (Outcome Other) :=
  match runPrelude prelude state with
  | .error fault => .error fault
  | .ok next => runProgram program next


/-! ### The decoded production symbol -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- Constructor form of the decoder's result on the committed bytes. Written
down by the untrusted `reduced%` elaborator and tied to the decoder by the
kernel-checked `symbol_decodes` below. -/
def decoded : List StackLoad × List Instruction :=
  reduced% ((decodeGoSymbol GoR51Object.symbolAddress
    GoR51Object.symbolBytes).getD ([], []))

def prelude : List StackLoad := decoded.1

def program : List Instruction := decoded.2

def body : List Instruction := program.take 127


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The exact 815 Go-linked bytes decode completely, to `decoded`. -/
theorem symbol_decodes :
    decodeGoSymbol GoR51Object.symbolAddress GoR51Object.symbolBytes =
      some (prelude, program) := by
  show decodeGoSymbol GoR51Object.symbolAddress GoR51Object.symbolBytes =
    some decoded
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The prelude loads `out`, `x`, and `y` from the three ABI0 argument slots,
and the vector program is 127 body instructions followed by `VZEROUPPER; RET`. -/
theorem decoded_shape :
    GoR51Object.symbolBytes.length = GoR51Object.symbolSize ∧
    prelude = [⟨.rdi, 8⟩, ⟨.rcx, 16⟩, ⟨.rbx, 24⟩] ∧
    program = body ++ epilogue ∧ program.length = 129 := by
  decide


/-- The linked read-only constants hold 19 and `2^51 - 1`. -/
theorem linked_constants :
    GoR51Object.ifmaFold19Bytes = [19, 0, 0, 0, 0, 0, 0, 0] ∧
    GoR51Object.ifmaLimbMask51Bytes = [255, 255, 255, 255, 255, 255, 7, 0] := by
  decide


/-! ### Checker run on the decoded body -/

/-- Go ABI0 contract data after the prelude: `x` rows through RCX, `y` rows
through RBX, the output object through RDI, and the two Go-linked constants. -/
def spec : LeafSpec :=
  { inputs := [
      ⟨.rcx, 0, 2 ^ 52 - 1⟩, ⟨.rcx, 64, 2 ^ 52 - 1⟩, ⟨.rcx, 128, 2 ^ 52 - 1⟩,
      ⟨.rcx, 192, 2 ^ 52 - 1⟩, ⟨.rcx, 256, 2 ^ 52 - 1⟩,
      ⟨.rbx, 0, 2 ^ 52 - 1⟩, ⟨.rbx, 64, 2 ^ 52 - 1⟩, ⟨.rbx, 128, 2 ^ 52 - 1⟩,
      ⟨.rbx, 192, 2 ^ 52 - 1⟩, ⟨.rbx, 256, 2 ^ 52 - 1⟩]
    constants := [
      ⟨GoR51Object.ifmaFold19Address, 19⟩,
      ⟨GoR51Object.ifmaLimbMask51Address, 2 ^ 51 - 1⟩]
    outputBase := .rdi
    outputBytes := 320 }


def final : SymState :=
  (runSym spec body initialSymState).getD initialSymState


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The checker accepts every decoded body instruction of the Go build. -/
theorem checker_accepts : runSym spec body initialSymState = some final := by
  apply eq_some_getD_of_isSome
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem output_bounds :
    (outputDefined final 0 = true ∧ outputBound final 0 < 2 ^ 52) ∧
    (outputDefined final 64 = true ∧ outputBound final 64 < 2 ^ 52) ∧
    (outputDefined final 128 = true ∧ outputBound final 128 < 2 ^ 52) ∧
    (outputDefined final 192 = true ∧ outputBound final 192 < 2 ^ 52) ∧
    (outputDefined final 256 = true ∧ outputBound final 256 < 2 ^ 52) := by
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


/-- The expressions computed from the Go-linked bytes are the same generated
scalar multiplication trace as for the standalone leaf, with `x` read through
RCX and `y` through RBX. -/
theorem outputs_are_assembly_output (inputs : Gpr → Nat → Nat) :
    (⟨(outputExpr final 0).eval inputs, (outputExpr final 64).eval inputs,
      (outputExpr final 128).eval inputs, (outputExpr final 192).eval inputs,
      (outputExpr final 256).eval inputs⟩ : Loose5) =
      assemblyOutput (inputLimbs inputs .rcx) (inputLimbs inputs .rbx) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := output_exprs
  obtain ⟨x0, x1, x2, x3, x4⟩ := R51Mul.inputLimbs_apply inputs .rcx
  obtain ⟨y0, y1, y2, y3, y4⟩ := R51Mul.inputLimbs_apply inputs .rbx
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


/-! ### Go ABI0 leaf theorem -/

/-- The three pointer arguments of `func(out, x, y *LimbsX8)` as the caller
left them on the stack: `out` at `8(SP)`, `x` at `16(SP)`, `y` at `24(SP)`. -/
def argOut (entry : MachineState Other) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsp) 8)

def argX (entry : MachineState Other) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsp) 16)

def argY (entry : MachineState Other) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsp) 24)


/-- Machine state after the argument prelude: memory and every other register
are unchanged, and RDI, RCX, RBX hold `out`, `x`, `y`. -/
def bodyEntry (entry : MachineState Other) : MachineState Other :=
  { entry with
    gpr := setGpr (setGpr (setGpr entry.gpr .rdi (argOut entry)) .rcx (argX entry))
      .rbx (argY entry) }


theorem bodyEntry_registers (entry : MachineState Other) :
    (bodyEntry entry).mem = entry.mem ∧
    (bodyEntry entry).gpr .rsp = entry.gpr .rsp ∧
    (bodyEntry entry).gpr .rdi = argOut entry ∧
    (bodyEntry entry).gpr .rcx = argX entry ∧
    (bodyEntry entry).gpr .rbx = argY entry := by
  simp [bodyEntry, setGpr]


theorem run_prelude (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true) :
    runPrelude prelude entry = .ok (bodyEntry entry) := by
  have h8 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 24 0 8 harguments (by omega)
  have h16 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 16) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 24 8 8 harguments (by omega)
  have h24 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 24) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 24 16 8 harguments (by omega)
  rw [decoded_shape.2.1]
  simp [runPrelude, execStackLoad, setGpr, h8, h16, h24, bodyEntry, argOut,
    argX, argY]


/-- Shared core: any leaf specification with the Go input rows and output
register whose checker run on `vectorBody` yields `final` gives the Go ABI0
leaf statement for the prelude followed by `vectorBody` and the epilogue. -/
theorem go_leaf_core (leafSpec : LeafSpec) (vectorBody : List Instruction)
    (hinputs : leafSpec.inputs = spec.inputs)
    (hbase : leafSpec.outputBase = Gpr.rdi)
    (haccepts : runSym leafSpec vectorBody initialSymState = some final)
    (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true)
    (hpre : LeafPre leafSpec lane (bodyEntry entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput leafSpec (bodyEntry entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude (vectorBody ++ epilogue) entry =
        .ok (.returned returned) ∧
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        (radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rcx) *
          radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rbx)) % P ∧
      (outputLimbs lane (bodyEntry entry) returned).l0 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l1 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l2 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l3 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l4 < 2 ^ 52 ∧
      LeafPost leafSpec lane final (bodyEntry entry) returned := by
  obtain ⟨hmem, hrsp, -, -, -⟩ := bodyEntry_registers entry
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
  obtain ⟨hlimbs, h0, h1, h2, h3, h4⟩ :=
    R51Mul.output_limbs_of_post_generic leafSpec final .rcx .rbx hbase
      output_bounds outputs_are_assembly_output lane (bodyEntry entry) returned
      hpost
  have hrow (base : Gpr) (displacement : Nat)
      (hmember : (⟨base, displacement, 2 ^ 52 - 1⟩ : InputRow) ∈ spec.inputs) :
      (⟨base, displacement, 2 ^ 52 - 1⟩ : InputRow) ∈ leafSpec.inputs := by
    rw [hinputs]
    exact hmember
  have htrace := AssemblyTrace.radix51_mul_assembly_trace_correct
    (inputLimbs (entryInputs lane (bodyEntry entry)) .rcx)
    (inputLimbs (entryInputs lane (bodyEntry entry)) .rbx)
    (R51Mul.input_limbs_u52 leafSpec lane (bodyEntry entry) hpre .rcx
      (hrow _ _ (by decide)) (hrow _ _ (by decide)) (hrow _ _ (by decide))
      (hrow _ _ (by decide)) (hrow _ _ (by decide)))
    (R51Mul.input_limbs_u52 leafSpec lane (bodyEntry entry) hpre .rbx
      (hrow _ _ (by decide)) (hrow _ _ (by decide)) (hrow _ _ (by decide))
      (hrow _ _ (by decide)) (hrow _ _ (by decide)))
  have hvalue :
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        (radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rcx) *
          radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rbx)) % P := by
    rw [hlimbs]
    exact htrace.1
  have hprogram : runGoSymbol prelude (vectorBody ++ epilogue) entry =
      .ok (.returned returned) := by
    unfold runGoSymbol
    rw [run_prelude entry harguments]
    exact hrun
  exact ⟨returned, hprogram, hvalue, h0, h1, h2, h3, h4, hpost⟩


/-- Leaf theorem for the production Go-linked multiplier bytes.

The committed 815 symbol bytes decode to a three-instruction argument prelude
and a 129-instruction vector program. From any entry state in which

* the three ABI0 argument slots at `8(SP)..31(SP)` are readable,
* `LeafPre spec lane` holds after the prelude: the ten 64-byte rows of `x` and
  `y` are readable with selected-lane values at most `2^52 - 1`, the two linked
  constants are readable with values 19 and `2^51 - 1`, and the 320-byte output
  object is writable,
* the return slot at `0(SP)` is readable and does not overlap the output,

the symbol returns normally, the selected lane of the output represents the
product of the selected-lane inputs modulo `2^255 - 19`, every output limb is
below `2^52`, and `LeafPost` holds relative to the post-prelude state.

`x`, `y`, and `out` may overlap arbitrarily, and the argument slots may overlap
the output, because every argument and input load precedes the first store. -/
theorem go_r51_multiplier_refines (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true)
    (hpre : LeafPre spec lane (bodyEntry entry))
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput spec (bodyEntry entry)
        (addressAdd (entry.gpr .rsp) offset)) :
    decodeGoSymbol GoR51Object.symbolAddress GoR51Object.symbolBytes =
        some (prelude, program) ∧
    ∃ returned,
      runGoSymbol prelude program entry = .ok (.returned returned) ∧
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        (radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rcx) *
          radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rbx)) % P ∧
      (outputLimbs lane (bodyEntry entry) returned).l0 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l1 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l2 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l3 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l4 < 2 ^ 52 ∧
      LeafPost spec lane final (bodyEntry entry) returned := by
  refine ⟨symbol_decodes, ?_⟩
  rw [decoded_shape.2.2.1]
  exact go_leaf_core spec body rfl rfl checker_accepts lane entry harguments
    hpre hreturn hstack


/-! ### Any link layout

A different binary that contains the same code links the two constants at
different addresses, so its decoded program differs from `program` exactly in
the two broadcast addresses. -/

/-- Rename the reference constant addresses to those of another link. -/
def relocation (fold19 mask51 : Nat) : Nat → Nat := fun address =>
  if address = GoR51Object.ifmaFold19Address then fold19
  else if address = GoR51Object.ifmaLimbMask51Address then mask51
  else address


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The body reads exactly the two declared constants, each once. -/
theorem body_broadcast_addresses :
    broadcastAddresses body =
      [GoR51Object.ifmaFold19Address, GoR51Object.ifmaLimbMask51Address] := by
  decide


theorem relocation_faithful (fold19 mask51 : Nat) (hdistinct : fold19 ≠ mask51) :
    RenameFaithful (relocation fold19 mask51) spec (broadcastAddresses body) := by
  rw [body_broadcast_addresses]
  intro constant hmember address haddress hequal
  simp only [spec, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hmember haddress
  rcases hmember with rfl | rfl <;> rcases haddress with rfl | rfl <;>
    simp_all [relocation, GoR51Object.ifmaFold19Address,
      GoR51Object.ifmaLimbMask51Address]


/-- The Go leaf theorem for any link layout: for arbitrary distinct constant
addresses `fold19` and `mask51`, the same prelude and the same vector program
with its two broadcast addresses renamed satisfy the same statement, with the
constants required at the renamed addresses. -/
theorem go_r51_multiplier_refines_relocated (fold19 mask51 : Nat)
    (hdistinct : fold19 ≠ mask51) (lane : Fin 8) (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true)
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
      looseValue (outputLimbs lane (bodyEntry entry) returned) % P =
        (radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rcx) *
          radixValue (inputLimbs (entryInputs lane (bodyEntry entry)) .rbx)) % P ∧
      (outputLimbs lane (bodyEntry entry) returned).l0 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l1 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l2 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l3 < 2 ^ 52 ∧
      (outputLimbs lane (bodyEntry entry) returned).l4 < 2 ^ 52 ∧
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


/-! ### Relation to the standalone leaf -/

/-- Rename the Go base registers and constant addresses to the standalone
System V leaf's. -/
def toStandalone : Instruction → Instruction
  | .vmovdqu64Load destination base displacement =>
      .vmovdqu64Load destination
        (match base with
          | .rcx => .rsi
          | .rbx => .rdx
          | other => other) displacement
  | .vpbroadcastq destination absoluteAddress =>
      .vpbroadcastq destination
        (if absoluteAddress = GoR51Object.ifmaFold19Address then
          R51Object.ifma_fold19Address
        else if absoluteAddress = GoR51Object.ifmaLimbMask51Address then
          R51Object.ifma_mask51Address
        else absoluteAddress)
  | instruction => instruction


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Cross-check: the Go build's decoded vector program is instruction for
instruction the standalone source-generated trace, up to the two input base
registers and the two constant addresses. The Go theorem above does not depend
on this fact. -/
theorem same_schedule_as_standalone :
    program.map toStandalone =
      GeneratedR51InstructionTrace.expectedProgram := by
  decide


/-! ### Non-vacuity -/

/-- Memory used only to show the Go leaf contract is satisfiable. -/
def witnessMemory : Memory :=
  { byte := fun address =>
      if address = BitVec.ofNat 64 GoR51Object.ifmaFold19Address then
        BitVec.ofNat 8 19
      else if address =
          BitVec.ofNat 64 (GoR51Object.ifmaLimbMask51Address + 6) then
        BitVec.ofNat 8 7
      else if BitVec.ofNat 64 GoR51Object.ifmaLimbMask51Address ≤ address ∧
          address < BitVec.ofNat 64 (GoR51Object.ifmaLimbMask51Address + 6) then
        BitVec.ofNat 8 255
      else BitVec.ofNat 8 0
    perm := fun _ => ⟨true, true, false⟩ }


/-- All three pointer arguments are zero and the stack pointer is `2^21`. -/
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


/-- The hypotheses of `go_r51_multiplier_refines` are jointly satisfiable for
lane zero. -/
theorem leaf_contract_satisfiable :
    readableBytes witnessEntry.mem
        (addressAdd (witnessEntry.gpr .rsp) 8) 24 = true ∧
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

end NaryaFormal.IfmaSym.GoR51Mul
