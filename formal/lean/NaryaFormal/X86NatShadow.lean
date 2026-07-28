/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Unbounded-natural shadow interpreter for one SIMD lane of the restricted r51
multiplier program. This interpreter deliberately omits machine wrapping. Its
IFMA operations use the mathematical split on operands that the later
machine-refinement theorem must prove are u52 at each program point.
-/

import NaryaFormal.AssemblyTrace
import NaryaFormal.X86Execution

namespace NaryaFormal.X86

open Radix51

structure NatShadowEnvironment where
  x : FiveLimbs
  y : FiveLimbs

structure NatShadowState where
  zmm : ZReg → Nat
  output : Fin 5 → Nat

inductive NatShadowOutcome
  | next (state : NatShadowState)
  | returned (state : NatShadowState)

def setNatZmm (registers : ZReg → Nat) (target : ZReg) (value : Nat) :
    ZReg → Nat :=
  fun register => if register = target then value else registers register

def setNatOutput (output : Fin 5 → Nat) (target : Fin 5) (value : Nat) :
    Fin 5 → Nat :=
  fun limb => if limb = target then value else output limb

def shadowLimbIndex (displacement : Nat) : Option (Fin 5) :=
  if displacement % 64 = 0 then
    let index := displacement / 64
    if hindex : index < 5 then some ⟨index, hindex⟩ else none
  else none

def shadowLoad (environment : NatShadowEnvironment) (base : Gpr)
    (displacement : Nat) : Option Nat := do
  let limb ← shadowLimbIndex displacement
  match base with
  | .rsi => some (environment.x limb)
  | .rdx => some (environment.y limb)
  | _ => none

def shadowConstant (absoluteAddress : Nat) : Option Nat :=
  if absoluteAddress = R51Object.ifma_fold19Address then some 19
  else if absoluteAddress = R51Object.ifma_mask51Address then some (2 ^ 51 - 1)
  else none

def writeNatZmm (state : NatShadowState) (target : ZReg) (value : Nat) :
    NatShadowState :=
  { state with zmm := setNatZmm state.zmm target value }

def executeNatShadow (environment : NatShadowEnvironment)
    (instruction : Instruction) (state : NatShadowState) :
    Option NatShadowOutcome :=
  match instruction with
  | .vmovdqu64Load destination base displacement => do
      let value ← shadowLoad environment base displacement
      some (.next (writeNatZmm state destination value))
  | .vmovdqu64Store base displacement source =>
      if base ≠ .rdi then none else do
      let limb ← shadowLimbIndex displacement
      some (.next { state with
        output := setNatOutput state.output limb (state.zmm source) })
  | .vpxorq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 ^^^ state.zmm source2)))
  | .vpmadd52luq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm destination + lo52 (state.zmm source1) (state.zmm source2))))
  | .vpmadd52huq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm destination + hi52 (state.zmm source1) (state.zmm source2))))
  | .vpaddq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 + state.zmm source2)))
  | .vpmullq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 * state.zmm source2)))
  | .vpandq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 &&& state.zmm source2)))
  | .vpsllq destination source amount =>
      some (.next (writeNatZmm state destination
        (state.zmm source * 2 ^ amount)))
  | .vpsrlq destination source amount =>
      some (.next (writeNatZmm state destination
        (state.zmm source / 2 ^ amount)))
  | .vpbroadcastq destination absoluteAddress => do
      let value ← shadowConstant absoluteAddress
      some (.next (writeNatZmm state destination value))
  | .vzeroUpper => some (.next state)
  | .ret => some (.returned state)

def runNatShadow (environment : NatShadowEnvironment) :
    List Instruction → NatShadowState → Option NatShadowOutcome
  | [], _ => none
  | instruction :: rest, state => do
      let outcome ← executeNatShadow environment instruction state
      match outcome with
      | .next nextState => runNatShadow environment rest nextState
      | .returned returnState =>
          if rest.isEmpty then some (.returned returnState) else none

/--
Execute a proof phase that must not contain `RET`. Unlike `runNatShadow`, the
empty instruction list is the identity. This makes source-generated schedule
phases independently characterizable and composable without expanding the
entire 129-instruction symbol into one enormous proof term.
-/
def runNatPhase (environment : NatShadowEnvironment) :
    List Instruction → NatShadowState → Option NatShadowState
  | [], state => some state
  | instruction :: rest, state => do
      let outcome ← executeNatShadow environment instruction state
      match outcome with
      | .next nextState => runNatPhase environment rest nextState
      | .returned _ => none

theorem runNatPhase_append (environment : NatShadowEnvironment)
    (first second : List Instruction) (state : NatShadowState) :
    runNatPhase environment (first ++ second) state = (do
      let middle ← runNatPhase environment first state
      runNatPhase environment second middle) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, runNatPhase]
      cases hstep : executeNatShadow environment instruction state with
      | none => simp [hstep]
      | some outcome =>
          cases outcome with
          | returned returnState => simp [hstep]
          | next nextState => simp [hstep, ih]

theorem runNatPhase_ret_rejected (environment : NatShadowEnvironment)
    (state : NatShadowState) :
    runNatPhase environment [.ret] state = none := by
  rfl

/--
If a non-returning prefix has a characterized result, peel that prefix from a
normal `runNatShadow` execution. This is the bridge between the independently
proved arithmetic phases and the actual trace runner, whose final `RET` must be
present and must be the last instruction.
-/
theorem runNatShadow_append_of_runNatPhase
    (environment : NatShadowEnvironment) (first suffix : List Instruction)
    (state middle : NatShadowState)
    (hphase : runNatPhase environment first state = some middle) :
    runNatShadow environment (first ++ suffix) state =
      runNatShadow environment suffix middle := by
  induction first generalizing state middle with
  | nil =>
      simp only [runNatPhase] at hphase
      cases hphase
      rfl
  | cons instruction rest ih =>
      simp only [runNatPhase] at hphase
      cases hstep : executeNatShadow environment instruction state with
      | none => simp [hstep] at hphase
      | some outcome =>
          cases outcome with
          | returned returnState => simp [hstep] at hphase
          | next nextState =>
              simp [hstep] at hphase
              simpa [runNatShadow, hstep] using
                (ih nextState middle hphase)

def initialNatShadowState : NatShadowState :=
  { zmm := fun _ => 0
    output := fun _ => 0 }

theorem and_mask51_eq_mod (value : Nat) :
    value &&& 2251799813685247 = value % 2251799813685248 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod value 51

def preparedNatZmm (environment : NatShadowEnvironment) (register : ZReg) : Nat :=
  match register.val with
  | 0 => environment.x 0
  | 1 => environment.x 1
  | 2 => environment.x 2
  | 3 => environment.x 3
  | 4 => environment.x 4
  | 5 => environment.y 0
  | 6 => environment.y 1
  | 7 => environment.y 2
  | 8 => environment.y 3
  | 9 => environment.y 4
  | _ => 0

def preparedNatShadowState (environment : NatShadowEnvironment) : NatShadowState :=
  { zmm := preparedNatZmm environment
    output := fun _ => 0 }

set_option maxRecDepth 4096 in
theorem prepare_phases_correct (environment : NatShadowEnvironment) :
    runNatPhase environment
      (GeneratedR51InstructionTrace.loadPhase ++
        GeneratedR51InstructionTrace.clearPhase)
      initialNatShadowState = some (preparedNatShadowState environment) := by
  simp [GeneratedR51InstructionTrace.loadPhase,
    GeneratedR51InstructionTrace.clearPhase, runNatPhase, executeNatShadow,
    shadowLoad, shadowLimbIndex, writeNatZmm, initialNatShadowState,
    preparedNatShadowState, preparedNatZmm, setNatZmm]
  funext register
  fin_cases register <;> rfl

def productNatZmm (environment : NatShadowEnvironment) (register : ZReg) : Nat :=
  match register.val with
  | 0 => environment.x 0
  | 1 => environment.x 1
  | 2 => environment.x 2
  | 3 => environment.x 3
  | 4 => environment.x 4
  | 5 => environment.y 0
  | 6 => environment.y 1
  | 7 => environment.y 2
  | 8 => environment.y 3
  | 9 => environment.y 4
  | 10 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 0).sum
  | 11 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 1).sum
  | 12 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 2).sum
  | 13 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 3).sum
  | 14 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 4).sum
  | 15 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 5).sum
  | 16 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 6).sum
  | 17 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 7).sum
  | 18 => (GeneratedR51MulTrace.lowTerms environment.x environment.y 8).sum
  | 19 => (GeneratedR51MulTrace.highTerms environment.x environment.y 0).sum
  | 20 => (GeneratedR51MulTrace.highTerms environment.x environment.y 1).sum
  | 21 => (GeneratedR51MulTrace.highTerms environment.x environment.y 2).sum
  | 22 => (GeneratedR51MulTrace.highTerms environment.x environment.y 3).sum
  | 23 => (GeneratedR51MulTrace.highTerms environment.x environment.y 4).sum
  | 24 => (GeneratedR51MulTrace.highTerms environment.x environment.y 5).sum
  | 25 => (GeneratedR51MulTrace.highTerms environment.x environment.y 6).sum
  | 26 => (GeneratedR51MulTrace.highTerms environment.x environment.y 7).sum
  | 27 => (GeneratedR51MulTrace.highTerms environment.x environment.y 8).sum
  | _ => 0

def productNatShadowState (environment : NatShadowEnvironment) : NatShadowState :=
  { zmm := productNatZmm environment
    output := fun _ => 0 }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem product_phase_correct (environment : NatShadowEnvironment) :
    runNatPhase environment GeneratedR51InstructionTrace.productPhase
      (preparedNatShadowState environment) =
      some (productNatShadowState environment) := by
  simp [GeneratedR51InstructionTrace.productPhase, runNatPhase,
    executeNatShadow, writeNatZmm, preparedNatShadowState, preparedNatZmm,
    productNatShadowState, setNatZmm]
  funext register
  fin_cases register <;>
    simp [setNatZmm, preparedNatZmm, productNatZmm,
      GeneratedR51MulTrace.lowTerms,
      GeneratedR51MulTrace.highTerms] <;> ring

def combinedNatZmm (environment : NatShadowEnvironment) (register : ZReg) : Nat :=
  match register.val with
  | 0 => environment.x 0
  | 1 => environment.x 1
  | 2 => environment.x 2
  | 3 => environment.x 3
  | 4 => environment.x 4
  | 5 => environment.y 0
  | 6 => environment.y 1
  | 7 => environment.y 2
  | 8 => environment.y 3
  | 9 => environment.y 4
  | 10 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 0
  | 11 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 1
  | 12 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 2
  | 13 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 3
  | 14 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 4
  | 15 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 5
  | 16 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 6
  | 17 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 7
  | 18 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 8
  | 19 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 0).sum
  | 20 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 1).sum
  | 21 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 2).sum
  | 22 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 3).sum
  | 23 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 4).sum
  | 24 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 5).sum
  | 25 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 6).sum
  | 26 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 7).sum
  | 27 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 9
  | _ => 0

def combinedNatShadowState (environment : NatShadowEnvironment) : NatShadowState :=
  { zmm := combinedNatZmm environment
    output := fun _ => 0 }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem combine_phase_correct (environment : NatShadowEnvironment) :
    runNatPhase environment GeneratedR51InstructionTrace.combinePhase
      (productNatShadowState environment) =
      some (combinedNatShadowState environment) := by
  simp [GeneratedR51InstructionTrace.combinePhase, runNatPhase,
    executeNatShadow, writeNatZmm, productNatShadowState,
    combinedNatShadowState, setNatZmm]
  funext register
  fin_cases register <;>
    simp [setNatZmm, productNatZmm, combinedNatZmm,
      GeneratedR51MulTrace.groupedDegree, GeneratedR51MulTrace.lowTerms,
      GeneratedR51MulTrace.highTerms] <;> ring

def foldedNatZmm (environment : NatShadowEnvironment) (register : ZReg) : Nat :=
  match register.val with
  | 0 => environment.x 0
  | 1 => environment.x 1
  | 2 => environment.x 2
  | 3 => environment.x 3
  | 4 => environment.x 4
  | 5 => environment.y 0
  | 6 => environment.y 1
  | 7 => environment.y 2
  | 8 => environment.y 3
  | 9 => environment.y 4
  | 10 => (GeneratedR51MulTrace.foldedGrouped environment.x environment.y).l0
  | 11 => (GeneratedR51MulTrace.foldedGrouped environment.x environment.y).l1
  | 12 => (GeneratedR51MulTrace.foldedGrouped environment.x environment.y).l2
  | 13 => (GeneratedR51MulTrace.foldedGrouped environment.x environment.y).l3
  | 14 => (GeneratedR51MulTrace.foldedGrouped environment.x environment.y).l4
  | 15 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 5
  | 16 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 6
  | 17 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 7
  | 18 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 8
  | 19 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 0).sum
  | 20 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 1).sum
  | 21 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 2).sum
  | 22 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 3).sum
  | 23 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 4).sum
  | 24 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 5).sum
  | 25 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 6).sum
  | 26 => 2 * (GeneratedR51MulTrace.highTerms environment.x environment.y 7).sum
  | 27 => GeneratedR51MulTrace.groupedDegree environment.x environment.y 9
  | 28 => 19 * GeneratedR51MulTrace.groupedDegree environment.x environment.y 9
  | 30 => 19
  | _ => 0

def foldedNatShadowState (environment : NatShadowEnvironment) : NatShadowState :=
  { zmm := foldedNatZmm environment
    output := fun _ => 0 }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem fold_phase_correct (environment : NatShadowEnvironment) :
    runNatPhase environment GeneratedR51InstructionTrace.foldPhase
      (combinedNatShadowState environment) =
      some (foldedNatShadowState environment) := by
  simp [GeneratedR51InstructionTrace.foldPhase, runNatPhase,
    executeNatShadow, shadowConstant, writeNatZmm, combinedNatShadowState,
    foldedNatShadowState, setNatZmm, R51Object.ifma_fold19Address,
    R51Object.ifma_mask51Address]
  funext register
  fin_cases register <;>
    simp [setNatZmm, combinedNatZmm, foldedNatZmm,
      GeneratedR51MulTrace.foldedGrouped,
      GeneratedR51MulTrace.foldConstant,
      GeneratedR51MulTrace.groupedDegree, GeneratedR51MulTrace.lowTerms,
      GeneratedR51MulTrace.highTerms] <;> ring

def normalizedNatZmm (environment : NatShadowEnvironment) (register : ZReg) : Nat :=
  let folded := GeneratedR51MulTrace.foldedGrouped environment.x environment.y
  let output := GeneratedR51MulTrace.assemblyOutput environment.x environment.y
  match register.val with
  | 5 => GeneratedR51MulTrace.traceMask
  | 10 => output.l0
  | 11 => output.l1
  | 12 => output.l2
  | 13 => output.l3
  | 14 => output.l4
  | 15 => GeneratedR51MulTrace.traceCarry folded.l0
  | 16 => GeneratedR51MulTrace.traceCarry folded.l1
  | 17 => GeneratedR51MulTrace.traceCarry folded.l2
  | 18 => GeneratedR51MulTrace.traceCarry folded.l3
  | 19 => GeneratedR51MulTrace.traceCarry folded.l4
  | _ => foldedNatZmm environment register

def normalizedNatShadowState (environment : NatShadowEnvironment) : NatShadowState :=
  { zmm := normalizedNatZmm environment
    output := fun _ => 0 }

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem normalize_phase_correct (environment : NatShadowEnvironment) :
    runNatPhase environment GeneratedR51InstructionTrace.normalizePhase
      (foldedNatShadowState environment) =
      some (normalizedNatShadowState environment) := by
  simp [GeneratedR51InstructionTrace.normalizePhase, runNatPhase,
    executeNatShadow, shadowConstant, writeNatZmm, foldedNatShadowState,
    normalizedNatShadowState, setNatZmm, R51Object.ifma_fold19Address,
    R51Object.ifma_mask51Address]
  funext register
  fin_cases register <;>
    simp [setNatZmm, normalizedNatZmm, foldedNatZmm,
      GeneratedR51MulTrace.assemblyOutput,
      GeneratedR51MulTrace.foldedGrouped,
      GeneratedR51MulTrace.traceMask, GeneratedR51MulTrace.traceCarry,
      GeneratedR51MulTrace.traceRemainder,
      GeneratedR51MulTrace.foldConstant,
      GeneratedR51MulTrace.groupedDegree, GeneratedR51MulTrace.lowTerms,
      GeneratedR51MulTrace.highTerms, and_mask51_eq_mod]

def storedNatShadowState (environment : NatShadowEnvironment) : NatShadowState :=
  let value := GeneratedR51MulTrace.assemblyOutput environment.x environment.y
  { zmm := normalizedNatZmm environment
    output := fun limb =>
      match limb.val with
      | 0 => value.l0
      | 1 => value.l1
      | 2 => value.l2
      | 3 => value.l3
      | _ => value.l4 }

set_option maxRecDepth 4096 in
theorem store_phase_correct (environment : NatShadowEnvironment) :
    runNatPhase environment GeneratedR51InstructionTrace.storePhase
      (normalizedNatShadowState environment) =
      some (storedNatShadowState environment) := by
  simp [GeneratedR51InstructionTrace.storePhase, runNatPhase,
    executeNatShadow, shadowLimbIndex, normalizedNatShadowState,
    storedNatShadowState, setNatOutput]
  funext limb
  fin_cases limb <;> rfl

def natShadowOutput (state : NatShadowState) : Loose5 :=
  { l0 := state.output 0
    l1 := state.output 1
    l2 := state.output 2
    l3 := state.output 3
    l4 := state.output 4 }

theorem stored_output_is_assembly_output (environment : NatShadowEnvironment) :
    natShadowOutput (storedNatShadowState environment) =
      GeneratedR51MulTrace.assemblyOutput environment.x environment.y := by
  rfl

/--
The exact 129-instruction program decoded from the linked ELF executes the
source-generated five-limb multiplication schedule in the unbounded-natural
shadow semantics and returns normally. This theorem deliberately says nothing
yet about 64-bit wraparound; the BitVec-to-Nat range bridge is a separate proof
obligation.
-/
theorem expected_program_returns_assembly_output
    (environment : NatShadowEnvironment) :
    runNatShadow environment GeneratedR51InstructionTrace.expectedProgram
      initialNatShadowState =
      some (.returned (storedNatShadowState environment)) := by
  rw [show GeneratedR51InstructionTrace.expectedProgram =
      (GeneratedR51InstructionTrace.loadPhase ++
        GeneratedR51InstructionTrace.clearPhase) ++
      (GeneratedR51InstructionTrace.productPhase ++
        (GeneratedR51InstructionTrace.combinePhase ++
          (GeneratedR51InstructionTrace.foldPhase ++
            (GeneratedR51InstructionTrace.normalizePhase ++
              (GeneratedR51InstructionTrace.storePhase ++
                GeneratedR51InstructionTrace.epiloguePhase))))) by
    simp [GeneratedR51InstructionTrace.expectedProgram, List.append_assoc]]
  rw [runNatShadow_append_of_runNatPhase environment _ _ _ _
    (prepare_phases_correct environment)]
  rw [runNatShadow_append_of_runNatPhase environment _ _ _ _
    (product_phase_correct environment)]
  rw [runNatShadow_append_of_runNatPhase environment _ _ _ _
    (combine_phase_correct environment)]
  rw [runNatShadow_append_of_runNatPhase environment _ _ _ _
    (fold_phase_correct environment)]
  rw [runNatShadow_append_of_runNatPhase environment _ _ _ _
    (normalize_phase_correct environment)]
  rw [runNatShadow_append_of_runNatPhase environment _ _ _ _
    (store_phase_correct environment)]
  rfl

def runR51NatShadow (x y : FiveLimbs) : Option Loose5 := do
  let outcome ← runNatShadow { x, y }
    GeneratedR51InstructionTrace.expectedProgram initialNatShadowState
  match outcome with
  | .returned state => some (natShadowOutput state)
  | .next _ => none

/--
The public Nat-shadow runner for the exact linked multiplier trace returns the
same loose radix-51 limbs as the independently generated arithmetic model.
-/
theorem runR51NatShadow_correct (x y : FiveLimbs) :
    runR51NatShadow x y =
      some (GeneratedR51MulTrace.assemblyOutput x y) := by
  rw [runR51NatShadow, expected_program_returns_assembly_output]
  rfl

end NaryaFormal.X86
