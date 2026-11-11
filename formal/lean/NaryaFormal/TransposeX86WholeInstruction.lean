/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Restricted whole-leaf instruction and execution model for the projective- and
affine-Niels transpose selectors.  The existing TransposeX86Decoder module owns
the proved eight-instruction shuffle network.  This file adds only the GPR,
permission-sensitive memory, mask, store, and epilogue operations surrounding
those blocks.
-/

import Mathlib
import NaryaFormal.TransposeX86Decoder
import NaryaFormal.X86Machine

namespace NaryaFormal.TransposeWholeX86

open NaryaFormal
open NaryaFormal.Transpose
open NaryaFormal.X86

abbrev Ymm := Q4 QWord

inductive Instruction
  | movReg64 (destination source : Gpr)
  | movLoad64 (destination base : Gpr) (displacement : Nat)
  | movImm32 (destination : Gpr) (value : Nat)
  | kmovb (destination : KReg) (source : Gpr)
  | ymmLoad (destination : ZReg) (base : Gpr) (displacement : Nat)
  | ymmMaskedLoad (destination : ZReg) (base : Gpr) (displacement : Nat)
      (mask : KReg) (zeroing : Bool)
  | ymmStore (base : Gpr) (displacement : Nat) (source : ZReg)
  | unpackLow (destination source1 source2 : ZReg)
  | unpackHigh (destination source1 source2 : ZReg)
  | shuffleI64x2 (destination source1 source2 : ZReg) (immediate : Nat)
  | vzeroUpper
  | ret
  deriving DecidableEq, Repr


def setKReg (registers : KReg → QWord) (target : KReg) (value : QWord) :
    KReg → QWord :=
  fun register => if register = target then value else registers register


def ymmOfZmm (value : Zmm) : Ymm :=
  ⟨value 0, value 1, value 2, value 3⟩


def zmmOfYmm (value : Ymm) : Zmm :=
  fun lane =>
    if lane = 0 then value.q0
    else if lane = 1 then value.q1
    else if lane = 2 then value.q2
    else if lane = 3 then value.q3
    else BitVec.ofNat 64 0


def loadYmm (memory : Memory) (base : Addr) : Ymm :=
  ⟨loadQwordLE memory (addressAdd base 0),
   loadQwordLE memory (addressAdd base 8),
   loadQwordLE memory (addressAdd base 16),
   loadQwordLE memory (addressAdd base 24)⟩


def maskBit (mask : QWord) (lane : Nat) : Bool :=
  mask.getLsbD lane


def readableMaskedYmm (memory : Memory) (base : Addr) (mask : QWord) : Bool :=
  (List.range 4).all (fun lane =>
    !maskBit mask lane || readableBytes memory (addressAdd base (8 * lane)) 8)


def loadMaskedYmm (memory : Memory) (base : Addr) (mask : QWord)
    (old : Ymm) (zeroing : Bool) : Ymm :=
  let disabled (oldValue : QWord) : QWord :=
    if zeroing then BitVec.ofNat 64 0 else oldValue
  ⟨if maskBit mask 0 then loadQwordLE memory (addressAdd base 0) else disabled old.q0,
   if maskBit mask 1 then loadQwordLE memory (addressAdd base 8) else disabled old.q1,
   if maskBit mask 2 then loadQwordLE memory (addressAdd base 16) else disabled old.q2,
   if maskBit mask 3 then loadQwordLE memory (addressAdd base 24) else disabled old.q3⟩


def storeYmm (memory : Memory) (base : Addr) (value : Ymm) : Memory :=
  let m0 := storeQwordLE memory (addressAdd base 0) value.q0
  let m1 := storeQwordLE m0 (addressAdd base 8) value.q1
  let m2 := storeQwordLE m1 (addressAdd base 16) value.q2
  storeQwordLE m2 (addressAdd base 24) value.q3


def ymmWrittenAddresses (base : Addr) (value : Ymm) : List Addr :=
  storeAddresses (addressAdd base 0) (qwordBytes value.q0) ++
  storeAddresses (addressAdd base 8) (qwordBytes value.q1) ++
  storeAddresses (addressAdd base 16) (qwordBytes value.q2) ++
  storeAddresses (addressAdd base 24) (qwordBytes value.q3)


def writeYmm {Other : Type} (state : MachineState Other) (target : ZReg)
    (value : Ymm) : MachineState Other :=
  { state with zmm := setZmm state.zmm target (zmmOfYmm value) }


def writeGpr {Other : Type} (state : MachineState Other) (target : Gpr)
    (value : QWord) : MachineState Other :=
  { state with gpr := setGpr state.gpr target value }


def writeKReg {Other : Type} (state : MachineState Other) (target : KReg)
    (value : QWord) : MachineState Other :=
  { state with opmask := setKReg state.opmask target value }


def execYmmLoad {Other : Type} (state : MachineState Other) (target : ZReg)
    (base : Addr) : Except Fault (MachineState Other) :=
  if readableBytes state.mem base 32 then
    .ok (writeYmm state target (loadYmm state.mem base))
  else
    .error (.readFault base)


def execYmmMaskedLoad {Other : Type} (state : MachineState Other)
    (target : ZReg) (base : Addr) (mask : KReg) (zeroing : Bool) :
    Except Fault (MachineState Other) :=
  let maskValue := state.opmask mask
  if readableMaskedYmm state.mem base maskValue then
    .ok (writeYmm state target
      (loadMaskedYmm state.mem base maskValue (ymmOfZmm (state.zmm target)) zeroing))
  else
    .error (.readFault base)


def execYmmStore {Other : Type} (state : MachineState Other) (base : Addr)
    (source : ZReg) : Except Fault (MachineState Other) :=
  if writableBytes state.mem base 32 then
    .ok { state with mem := storeYmm state.mem base (ymmOfZmm (state.zmm source)) }
  else
    .error (.writeFault base)


def executeInstruction {Other : Type} (instruction : Instruction)
    (state : MachineState Other) : Except Fault (Outcome Other) :=
  match instruction with
  | .movReg64 destination source =>
      .ok (.next (writeGpr state destination (state.gpr source)))
  | .movLoad64 destination base displacement =>
      let address := addressAdd (state.gpr base) displacement
      if readableBytes state.mem address 8 then
        .ok (.next (writeGpr state destination (loadQwordLE state.mem address)))
      else
        .error (.readFault address)
  | .movImm32 destination value =>
      .ok (.next (writeGpr state destination (BitVec.ofNat 64 (value % 2 ^ 32))))
  | .kmovb destination source =>
      .ok (.next (writeKReg state destination
        (BitVec.ofNat 64 ((state.gpr source).toNat % 2 ^ 8))))
  | .ymmLoad destination base displacement =>
      (execYmmLoad state destination (addressAdd (state.gpr base) displacement)).map .next
  | .ymmMaskedLoad destination base displacement mask zeroing =>
      (execYmmMaskedLoad state destination
        (addressAdd (state.gpr base) displacement) mask zeroing).map .next
  | .ymmStore base displacement source =>
      (execYmmStore state (addressAdd (state.gpr base) displacement) source).map .next
  | .unpackLow destination source1 source2 =>
      .ok (.next (writeYmm state destination
        (unpackLowQword (ymmOfZmm (state.zmm source1))
          (ymmOfZmm (state.zmm source2)))))
  | .unpackHigh destination source1 source2 =>
      .ok (.next (writeYmm state destination
        (unpackHighQword (ymmOfZmm (state.zmm source1))
          (ymmOfZmm (state.zmm source2)))))
  | .shuffleI64x2 destination source1 source2 immediate =>
      .ok (.next (writeYmm state destination
        (shuffleI64x2Ymm immediate (ymmOfZmm (state.zmm source1))
          (ymmOfZmm (state.zmm source2)))))
  | .vzeroUpper => .ok (.next (execVzeroUpper state))
  | .ret => execRet state


def runProgram {Other : Type} :
    List Instruction → MachineState Other → Except Fault (Outcome Other)
  | [], _ => .error .badDecode
  | instruction :: rest, state =>
      match executeInstruction instruction state with
      | .error fault => .error fault
      | .ok (.next nextState) => runProgram rest nextState
      | .ok (.returned returnState) =>
          if rest.isEmpty then .ok (.returned returnState) else .error .badDecode


def runPhase {Other : Type} :
    List Instruction → MachineState Other → Except Fault (MachineState Other)
  | [], state => .ok state
  | instruction :: rest, state =>
      match executeInstruction instruction state with
      | .error fault => .error fault
      | .ok (.next nextState) => runPhase rest nextState
      | .ok (.returned _) => .error .badDecode


theorem runPhase_append {Other : Type} (first second : List Instruction)
    (state : MachineState Other) :
    runPhase (first ++ second) state = (do
      let middle ← runPhase first state
      runPhase second middle) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, runPhase]
      cases hstep : executeInstruction instruction state with
      | error fault => rfl
      | ok outcome =>
          cases outcome with
          | returned returnState => rfl
          | next nextState => simp [hstep, ih]


/-- Peel a successfully executed non-returning body from normal execution. -/
theorem runProgram_append_of_runPhase {Other : Type}
    (first suffix : List Instruction) (state middle : MachineState Other)
    (hphase : runPhase first state = .ok middle) :
    runProgram (first ++ suffix) state = runProgram suffix middle := by
  induction first generalizing state middle with
  | nil =>
      simp only [runPhase] at hphase
      cases hphase
      rfl
  | cons instruction rest ih =>
      simp only [runPhase] at hphase
      cases hstep : executeInstruction instruction state with
      | error fault => simp [hstep] at hphase
      | ok outcome =>
          cases outcome with
          | returned returnState => simp [hstep] at hphase
          | next nextState =>
              simp [hstep] at hphase
              simpa [runProgram, hstep] using ih nextState middle hphase


theorem readableMaskedYmm_seven (memory : Memory) (base : Addr) :
    readableMaskedYmm memory base (BitVec.ofNat 64 7) =
      (readableBytes memory (addressAdd base 0) 8 &&
       readableBytes memory (addressAdd base 8) 8 &&
       readableBytes memory (addressAdd base 16) 8) := by
  have hrange : List.range 4 = [0, 1, 2, 3] := by decide
  have hbit1 : Nat.testBit 7 1 = true := by decide
  have hbit2 : Nat.testBit 7 2 = true := by decide
  have hbit3 : Nat.testBit 7 3 = false := by decide
  rw [readableMaskedYmm, hrange]
  simp [maskBit, BitVec.getLsbD, hbit1, hbit2, hbit3]
  cases readableBytes memory (addressAdd base 0) 8 <;>
    cases readableBytes memory (addressAdd base 8) 8 <;>
    cases readableBytes memory (addressAdd base 16) 8 <;> decide


/-- The guard-page contract: no readability premise for `base+24` occurs. -/
theorem readableMaskedYmm_seven_of_three
    (memory : Memory) (base : Addr)
    (h0 : readableBytes memory (addressAdd base 0) 8 = true)
    (h1 : readableBytes memory (addressAdd base 8) 8 = true)
    (h2 : readableBytes memory (addressAdd base 16) 8 = true) :
    readableMaskedYmm memory base (BitVec.ofNat 64 7) = true := by
  rw [readableMaskedYmm_seven, h0, h1, h2]
  decide


theorem loadMaskedYmm_seven_zero (memory : Memory) (base : Addr) (old : Ymm) :
    loadMaskedYmm memory base (BitVec.ofNat 64 7) old true =
      ⟨loadQwordLE memory (addressAdd base 0),
       loadQwordLE memory (addressAdd base 8),
       loadQwordLE memory (addressAdd base 16),
       BitVec.ofNat 64 0⟩ := by
  simp [loadMaskedYmm, maskBit]


theorem storeYmm_permissions (memory : Memory) (base : Addr) (value : Ymm) :
    (storeYmm memory base value).perm = memory.perm := by
  simp [storeYmm, storeQwordLE_permissions]


theorem storeYmm_frame (memory : Memory) (base candidate : Addr) (value : Ymm)
    (hnot : candidate ∉ ymmWrittenAddresses base value) :
    (storeYmm memory base value).byte candidate = memory.byte candidate := by
  simp only [ymmWrittenAddresses, List.mem_append, not_or] at hnot
  rcases hnot with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  simp only [storeYmm]
  rw [storeQwordLE_frame _ _ _ _ h3]
  rw [storeQwordLE_frame _ _ _ _ h2]
  rw [storeQwordLE_frame _ _ _ _ h1]
  rw [storeQwordLE_frame _ _ _ _ h0]


theorem ymmOfZmm_zmmOfYmm (value : Ymm) : ymmOfZmm (zmmOfYmm value) = value := by
  cases value
  rfl


theorem zmmOfYmm_upper_zero (value : Ymm) (lane : Fin 8) (hlane : 4 ≤ lane.val) :
    zmmOfYmm value lane = BitVec.ofNat 64 0 := by
  have h0 : lane.val ≠ 0 := by omega
  have h1 : lane.val ≠ 1 := by omega
  have h2 : lane.val ≠ 2 := by omega
  have h3 : lane.val ≠ 3 := by omega
  have h0' : lane ≠ (0 : Fin 8) := by omega
  have h1' : lane ≠ (1 : Fin 8) := by omega
  have h2' : lane ≠ (2 : Fin 8) := by omega
  have h3' : lane ≠ (3 : Fin 8) := by omega
  simp [zmmOfYmm, h0', h1', h2', h3']

end NaryaFormal.TransposeWholeX86
