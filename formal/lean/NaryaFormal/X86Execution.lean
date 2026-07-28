/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Execution semantics for the restricted decoded instruction language. The
decoder has already resolved instruction boundaries, register extensions,
compressed displacements, and RIP-relative constant addresses. This layer
models architectural data effects and faults; instruction fetch, canonical
address policy, CET, and asynchronous memory mutation remain outside it.
-/

import NaryaFormal.X86ObjectRefinement

namespace NaryaFormal.X86

def writeZmm {Other : Type} (state : MachineState Other) (target : ZReg)
    (value : Zmm) : MachineState Other :=
  { state with zmm := setZmm state.zmm target value }

def broadcastQword (value : QWord) : Zmm := fun _ => value

def execBroadcast {Other : Type} (state : MachineState Other)
    (destination : ZReg) (absoluteAddress : Nat) :
    Except Fault (MachineState Other) :=
  if _haddress : absoluteAddress < 2 ^ 64 then
    let address : Addr := BitVec.ofNat 64 absoluteAddress
    if readableBytes state.mem address 8 then
      .ok (writeZmm state destination
        (broadcastQword (loadQwordLE state.mem address)))
    else
      .error (.readFault address)
  else
    .error (.addressOutOfRange (BitVec.ofNat 64 absoluteAddress))

def executeInstruction {Other : Type} (instruction : Instruction)
    (state : MachineState Other) : Except Fault (Outcome Other) :=
  match instruction with
  | .vmovdqu64Load destination base displacement =>
      (execVmovdqu64Load state destination
        (addressAdd (state.gpr base) displacement)).map .next
  | .vmovdqu64Store base displacement source =>
      (execVmovdqu64Store state
        (addressAdd (state.gpr base) displacement) source).map .next
  | .vpxorq destination source1 source2 =>
      .ok (.next (writeZmm state destination
        (vpxorq (state.zmm source1) (state.zmm source2))))
  | .vpmadd52luq destination source1 source2 =>
      .ok (.next (writeZmm state destination
        (vpmadd52luq (state.zmm destination)
          (state.zmm source1) (state.zmm source2))))
  | .vpmadd52huq destination source1 source2 =>
      .ok (.next (writeZmm state destination
        (vpmadd52huq (state.zmm destination)
          (state.zmm source1) (state.zmm source2))))
  | .vpaddq destination source1 source2 =>
      .ok (.next (writeZmm state destination
        (vpaddq (state.zmm source1) (state.zmm source2))))
  | .vpmullq destination source1 source2 =>
      .ok (.next (writeZmm state destination
        (vpmullq (state.zmm source1) (state.zmm source2))))
  | .vpandq destination source1 source2 =>
      .ok (.next (writeZmm state destination
        (vpandq (state.zmm source1) (state.zmm source2))))
  | .vpsllq destination source amount =>
      .ok (.next (writeZmm state destination
        (vpsllq (state.zmm source) amount)))
  | .vpsrlq destination source amount =>
      .ok (.next (writeZmm state destination
        (vpsrlq (state.zmm source) amount)))
  | .vpbroadcastq destination absoluteAddress =>
      (execBroadcast state destination absoluteAddress).map .next
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
          if rest.isEmpty then .ok (.returned returnState)
          else .error .badDecode

/--
Execute a machine-proof phase that must not contain `RET`. The empty list is
the identity, so independently audited schedule phases compose without
unfolding the full linked program into one proof term.
-/
def runMachinePhase {Other : Type} :
    List Instruction → MachineState Other → Except Fault (MachineState Other)
  | [], state => .ok state
  | instruction :: rest, state =>
      match executeInstruction instruction state with
      | .error fault => .error fault
      | .ok (.next nextState) => runMachinePhase rest nextState
      | .ok (.returned _) => .error .badDecode

theorem runMachinePhase_append {Other : Type} (first second : List Instruction)
    (state : MachineState Other) :
    runMachinePhase (first ++ second) state = (do
      let middle ← runMachinePhase first state
      runMachinePhase second middle) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, runMachinePhase]
      cases hstep : executeInstruction instruction state with
      | error fault =>
          simp only [hstep]
          rfl
      | ok outcome =>
          cases outcome with
          | returned returnState =>
              simp only [hstep]
              rfl
          | next nextState => simp [hstep, ih]

/-- Peel a successfully executed non-returning prefix from normal execution. -/
theorem runProgram_append_of_runMachinePhase {Other : Type}
    (first suffix : List Instruction) (state middle : MachineState Other)
    (hphase : runMachinePhase first state = .ok middle) :
    runProgram (first ++ suffix) state = runProgram suffix middle := by
  induction first generalizing state middle with
  | nil =>
      simp only [runMachinePhase] at hphase
      cases hphase
      rfl
  | cons instruction rest ih =>
      simp only [runMachinePhase] at hphase
      cases hstep : executeInstruction instruction state with
      | error fault => simp [hstep] at hphase
      | ok outcome =>
          cases outcome with
          | returned returnState => simp [hstep] at hphase
          | next nextState =>
              simp [hstep] at hphase
              simpa [runProgram, hstep] using ih nextState middle hphase

theorem execute_vpxorq {Other : Type} (state : MachineState Other)
    (destination source1 source2 : ZReg) :
    executeInstruction (.vpxorq destination source1 source2) state =
      .ok (.next (writeZmm state destination
        (vpxorq (state.zmm source1) (state.zmm source2)))) := by
  rfl

theorem execute_vpmadd52luq_lane {Other : Type} (state : MachineState Other)
    (destination source1 source2 : ZReg) :
    executeInstruction (.vpmadd52luq destination source1 source2) state =
      .ok (.next (writeZmm state destination
        (vpmadd52luq (state.zmm destination)
          (state.zmm source1) (state.zmm source2)))) := by
  rfl

theorem executeBroadcast_unreadable {Other : Type} (state : MachineState Other)
    (destination : ZReg) (absoluteAddress : Nat)
    (haddress : absoluteAddress < 2 ^ 64)
    (hread : readableBytes state.mem (BitVec.ofNat 64 absoluteAddress) 8 = false) :
    execBroadcast state destination absoluteAddress =
      .error (.readFault (BitVec.ofNat 64 absoluteAddress)) := by
  norm_num at haddress
  simp [execBroadcast, haddress, hread]

theorem executeBroadcast_readable {Other : Type} (state : MachineState Other)
    (destination : ZReg) (absoluteAddress : Nat)
    (haddress : absoluteAddress < 2 ^ 64)
    (hread : readableBytes state.mem (BitVec.ofNat 64 absoluteAddress) 8 = true) :
    execBroadcast state destination absoluteAddress =
      .ok (writeZmm state destination
        (broadcastQword
          (loadQwordLE state.mem (BitVec.ofNat 64 absoluteAddress)))) := by
  norm_num at haddress
  simp [execBroadcast, haddress, hread]

theorem runProgram_rejects_trailing_after_ret {Other : Type}
    (state : MachineState Other) (instruction : Instruction) :
    runProgram [.ret, instruction] state =
      match execRet state with
      | .error fault => .error fault
      | .ok _ => .error .badDecode := by
  by_cases hread : readableBytes state.mem (state.gpr Gpr.rsp) 8 = true
  · rw [execRet_readable state hread]
    simp [runProgram, executeInstruction, execRet, hread]
  · have hfalse : readableBytes state.mem (state.gpr Gpr.rsp) 8 = false :=
      Bool.eq_false_of_not_eq_true hread
    rw [execRet_unreadable state hfalse]
    simp [runProgram, executeInstruction, execRet, hfalse]

end NaryaFormal.X86
