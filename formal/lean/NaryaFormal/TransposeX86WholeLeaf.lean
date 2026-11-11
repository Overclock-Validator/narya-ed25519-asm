/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Value-parametric symbolic executor for the non-returning bodies of the exact
relocation-free projective- and affine-Niels transpose leaves.

Source qwords are opaque tokens, so the lane-map certificates below cannot
succeed by arithmetic cancellation or by choosing convenient test values. The
executor is partial: it returns `none` for every instruction instance it cannot
justify (unknown base register, unknown opmask, out-of-bounds or misaligned
displacement, and `RET`).

This file is a certificate *about the symbolic executor*. The link to the
byte-addressed machine model is `executeSym_sound` in
`TransposeX86WholeSoundness.lean`; the whole-leaf machine theorems are stated
there. Nothing in this file should be cited as a machine-level claim on its own.
-/

import NaryaFormal.TransposeX86WholeDecoder

namespace NaryaFormal.TransposeWholeX86

open NaryaFormal.X86
open NaryaFormal.Transpose

/-- One opaque 64-bit value. `source lane byteOffset` is the qword stored at
`byteOffset` bytes into the source object selected for output lane `lane`. -/
inductive Cell
  | source (lane byteOffset : Nat)
  | zero
  | entryYmm (register lane : Nat)
  deriving DecidableEq, Repr

inductive SymWord
  | entry (register : Gpr)
  | output
  | pointerTable
  | sourcePointer (lane : Nat)
  | constant (value : Nat)
  deriving DecidableEq, Repr

structure SymEnvironment where
  /-- Bytes per limb row of one source object. -/
  rowBytes : Nat
  /-- Exact byte length of one source object; nothing beyond it may be read. -/
  sourceBytes : Nat
  /-- Exact byte length of the output object; nothing beyond it may be written. -/
  outputBytes : Nat
  deriving DecidableEq, Repr

/-- `gpr`, `ymm`, `opmask`, and `output` are related to the concrete machine by
the simulation theorem. `pointerReads` and `reads` are an auxiliary access log
of the symbolic executor only. -/
structure SymState where
  gpr : Gpr → SymWord
  ymm : ZReg → Q4 Cell
  opmask : KReg → Option Nat
  output : Nat → Option Cell
  pointerReads : List Nat
  reads : List (Nat × Nat)


def initialSymState : SymState :=
  { gpr := fun register =>
      if register = .rdi then .output
      else if register = .rsi then .pointerTable
      else .entry register
    ymm := fun register =>
      ⟨.entryYmm register.val 0, .entryYmm register.val 1,
       .entryYmm register.val 2, .entryYmm register.val 3⟩
    opmask := fun _ => none
    output := fun _ => none
    pointerReads := []
    reads := [] }


def setSymGpr (registers : Gpr → SymWord) (target : Gpr) (value : SymWord) :
    Gpr → SymWord :=
  fun register => if register = target then value else registers register


def setSymYmm (registers : ZReg → Q4 Cell) (target : ZReg) (value : Q4 Cell) :
    ZReg → Q4 Cell :=
  fun register => if register = target then value else registers register


def setSymMask (registers : KReg → Option Nat) (target : KReg)
    (value : Option Nat) : KReg → Option Nat :=
  fun register => if register = target then value else registers register


def setSymOutput (output : Nat → Option Cell) (offset : Nat) (value : Cell) :
    Nat → Option Cell :=
  fun candidate => if candidate = offset then some value else output candidate


def loadedCells (sourceLane displacement : Nat) : Q4 Cell :=
  ⟨.source sourceLane displacement, .source sourceLane (displacement + 8),
   .source sourceLane (displacement + 16), .source sourceLane (displacement + 24)⟩


def loadedReads (sourceLane displacement : Nat) : List (Nat × Nat) :=
  [(sourceLane, displacement), (sourceLane, displacement + 8),
   (sourceLane, displacement + 16), (sourceLane, displacement + 24)]


/-- EVEX merge/zero masking of one qword. A masked-off qword never becomes a
source token, so it can never require source readability. -/
def maskedCell (sourceLane byteOffset mask qword : Nat) (zeroing : Bool)
    (old : Cell) : Cell :=
  if mask.testBit qword then .source sourceLane byteOffset
  else if zeroing then .zero else old


def maskedCells (sourceLane displacement mask : Nat) (zeroing : Bool)
    (old : Q4 Cell) : Q4 Cell :=
  ⟨maskedCell sourceLane displacement mask 0 zeroing old.q0,
   maskedCell sourceLane (displacement + 8) mask 1 zeroing old.q1,
   maskedCell sourceLane (displacement + 16) mask 2 zeroing old.q2,
   maskedCell sourceLane (displacement + 24) mask 3 zeroing old.q3⟩


def maskedReads (sourceLane displacement mask : Nat) : List (Nat × Nat) :=
  (if mask.testBit 0 then [(sourceLane, displacement)] else []) ++
  (if mask.testBit 1 then [(sourceLane, displacement + 8)] else []) ++
  (if mask.testBit 2 then [(sourceLane, displacement + 16)] else []) ++
  (if mask.testBit 3 then [(sourceLane, displacement + 24)] else [])


/-- Only the enabled qwords must lie inside the source object. -/
def MaskedLoadInBounds (environment : SymEnvironment)
    (displacement mask : Nat) : Prop :=
  (mask.testBit 0 = true → displacement + 8 ≤ environment.sourceBytes) ∧
  (mask.testBit 1 = true → displacement + 16 ≤ environment.sourceBytes) ∧
  (mask.testBit 2 = true → displacement + 24 ≤ environment.sourceBytes) ∧
  (mask.testBit 3 = true → displacement + 32 ≤ environment.sourceBytes)


instance (environment : SymEnvironment) (displacement mask : Nat) :
    Decidable (MaskedLoadInBounds environment displacement mask) := by
  unfold MaskedLoadInBounds
  infer_instance


def symStoreYmm (state : SymState) (offset : Nat) (value : Q4 Cell) : SymState :=
  { state with
    output := setSymOutput
      (setSymOutput
        (setSymOutput
          (setSymOutput state.output offset value.q0)
          (offset + 8) value.q1)
        (offset + 16) value.q2)
      (offset + 24) value.q3 }


/-- `VZEROUPPER` clears bits 128 and above of ZMM0--ZMM15. -/
def vzeroUpperCells (register : ZReg) (value : Q4 Cell) : Q4 Cell :=
  if register.val < 16 then ⟨value.q0, value.q1, .zero, .zero⟩ else value


def executeSym (environment : SymEnvironment) (instruction : Instruction)
    (state : SymState) : Option SymState :=
  match instruction with
  | .movReg64 destination source =>
      some { state with gpr := setSymGpr state.gpr destination (state.gpr source) }
  | .movLoad64 destination base displacement =>
      if state.gpr base = .pointerTable ∧ displacement % 8 = 0 ∧
          displacement < 64 then
        some { state with
          gpr := setSymGpr state.gpr destination (.sourcePointer (displacement / 8))
          pointerReads := state.pointerReads ++ [displacement] }
      else none
  | .movImm32 destination value =>
      some { state with
        gpr := setSymGpr state.gpr destination (.constant (value % 2 ^ 32)) }
  | .kmovb destination source =>
      match state.gpr source with
      | .constant value =>
          some { state with
            opmask := setSymMask state.opmask destination (some (value % 2 ^ 8)) }
      | _ => none
  | .ymmLoad destination base displacement =>
      match state.gpr base with
      | .sourcePointer sourceLane =>
          if displacement + 32 ≤ environment.sourceBytes then
            some { state with
              ymm := setSymYmm state.ymm destination
                (loadedCells sourceLane displacement)
              reads := state.reads ++ loadedReads sourceLane displacement }
          else none
      | _ => none
  | .ymmMaskedLoad destination base displacement mask zeroing =>
      match state.gpr base with
      | .sourcePointer sourceLane =>
          match state.opmask mask with
          | some maskValue =>
              if MaskedLoadInBounds environment displacement maskValue then
                some { state with
                  ymm := setSymYmm state.ymm destination
                    (maskedCells sourceLane displacement maskValue zeroing
                      (state.ymm destination))
                  reads := state.reads ++
                    maskedReads sourceLane displacement maskValue }
              else none
          | none => none
      | _ => none
  | .ymmStore base displacement source =>
      if state.gpr base = .output ∧ displacement % 8 = 0 ∧
          displacement + 32 ≤ environment.outputBytes then
        some (symStoreYmm state displacement (state.ymm source))
      else none
  | .unpackLow destination source1 source2 =>
      some { state with
        ymm := setSymYmm state.ymm destination
          (unpackLowQword (state.ymm source1) (state.ymm source2)) }
  | .unpackHigh destination source1 source2 =>
      some { state with
        ymm := setSymYmm state.ymm destination
          (unpackHighQword (state.ymm source1) (state.ymm source2)) }
  | .shuffleI64x2 destination source1 source2 immediate =>
      some { state with
        ymm := setSymYmm state.ymm destination
          (shuffleI64x2Ymm immediate (state.ymm source1) (state.ymm source2)) }
  | .vzeroUpper =>
      some { state with
        ymm := fun register => vzeroUpperCells register (state.ymm register) }
  | .ret => none


def runSym (environment : SymEnvironment) :
    List Instruction → SymState → Option SymState
  | [], state => some state
  | instruction :: rest, state =>
      match executeSym environment instruction state with
      | some next => runSym environment rest next
      | none => none


def projectiveEnvironment : SymEnvironment :=
  { rowBytes := 32, sourceBytes := 160, outputBytes := 1280 }


def affineEnvironment : SymEnvironment :=
  { rowBytes := 24, sourceBytes := 120, outputBytes := 960 }


def projectiveFinal : SymState :=
  (runSym projectiveEnvironment Generated.projectiveBody initialSymState).getD
    initialSymState


def affineFinal : SymState :=
  (runSym affineEnvironment Generated.affineBody initialSymState).getD
    initialSymState


def expectedOutputCell (environment : SymEnvironment)
    (coordinate limb lane : Nat) : Cell :=
  .source lane (environment.rowBytes * limb + 8 * coordinate)


def outputOffset (coordinate limb lane : Nat) : Nat :=
  320 * coordinate + 64 * limb + 8 * lane


theorem eq_some_getD_of_isSome {α : Type} (value : Option α) (fallback : α)
    (hsome : value.isSome = true) : value = some (value.getD fallback) := by
  cases value with
  | none => cases hsome
  | some _ => rfl


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem projective_symbolic_execution_succeeds :
    runSym projectiveEnvironment Generated.projectiveBody initialSymState =
      some projectiveFinal := by
  apply eq_some_getD_of_isSome
  decide


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem affine_symbolic_execution_succeeds :
    runSym affineEnvironment Generated.affineBody initialSymState =
      some affineFinal := by
  apply eq_some_getD_of_isSome
  decide


set_option maxRecDepth 4096 in
theorem projective_body_has_no_ret :
    Instruction.ret ∉ Generated.projectiveBody := by
  decide


set_option maxRecDepth 4096 in
theorem affine_body_has_no_ret :
    Instruction.ret ∉ Generated.affineBody := by
  decide


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem projective_complete_lane_map :
    ∀ coordinate : Fin 4, ∀ limb : Fin 5, ∀ lane : Fin 8,
      projectiveFinal.output
          (outputOffset coordinate.val limb.val lane.val) =
        some (expectedOutputCell projectiveEnvironment
          coordinate.val limb.val lane.val) := by
  decide


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem affine_complete_lane_map :
    ∀ coordinate : Fin 3, ∀ limb : Fin 5, ∀ lane : Fin 8,
      affineFinal.output
          (outputOffset coordinate.val limb.val lane.val) =
        some (expectedOutputCell affineEnvironment
          coordinate.val limb.val lane.val) := by
  decide


/-- Symbolic register facts consumed by the machine-level return theorem: the
output pointer is returned in RAX, the stack pointer and every System V
callee-saved GPR still hold their entry values, and the eight pointer-table
slots were consumed in order. -/
def SymbolicRegisterContract (final : SymState) : Prop :=
  final.gpr .rax = .output ∧
  final.gpr .rsp = .entry .rsp ∧
  final.gpr .rbx = .entry .rbx ∧
  final.gpr .rbp = .entry .rbp ∧
  final.gpr .r12 = .entry .r12 ∧
  final.gpr .r13 = .entry .r13 ∧
  final.gpr .r14 = .entry .r14 ∧
  final.gpr .r15 = .entry .r15 ∧
  final.pointerReads = [0, 8, 16, 24, 32, 40, 48, 56]


instance (final : SymState) : Decidable (SymbolicRegisterContract final) := by
  unfold SymbolicRegisterContract
  infer_instance


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem projective_register_contract :
    SymbolicRegisterContract projectiveFinal := by
  decide


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem affine_register_contract :
    SymbolicRegisterContract affineFinal ∧ affineFinal.opmask 1 = some 7 := by
  decide


/-! ### Symbolic access log

These certificates describe which source qwords the symbolic executor
requested. The machine-level counterpart is stated in
`TransposeX86WholeSoundness.lean`: execution cannot fault when only the exact
source objects are readable. The output frame has no symbolic log: the machine
theorem proves that no byte outside the output object changes, and the lane
maps above determine every qword inside it. -/

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
/-- The affine trace never requests the masked fourth qword of the last row:
`(lane,120)` is absent for every source. -/
theorem affine_masked_tail_not_read :
    ∀ source : Fin 8, (source.val, 120) ∉ affineFinal.reads := by
  decide


def expectedProjectiveReads : Finset (Nat × Nat) :=
  ((Finset.range 8).product ((Finset.range 5).product (Finset.range 4))).image
    (fun item => (item.1, 32 * item.2.1 + 8 * item.2.2))


def expectedAffineReads : Finset (Nat × Nat) :=
  ((Finset.range 8).product ((Finset.range 5).product (Finset.range 3))).image
    (fun item => (item.1, 24 * item.2.1 + 8 * item.2.2))


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem projective_exact_source_read_set :
    projectiveFinal.reads.Nodup ∧
      projectiveFinal.reads.toFinset = expectedProjectiveReads := by
  decide


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem affine_exact_source_read_set :
    affineFinal.reads.Nodup ∧
      affineFinal.reads.toFinset = expectedAffineReads := by
  decide

end NaryaFormal.TransposeWholeX86
