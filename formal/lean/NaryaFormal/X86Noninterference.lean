/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Semantic noninterference for caller-owned ZMM scratch registers. The static
definite-assignment certificate proves that the decoded arithmetic core never
reads an undefined register. This file connects that syntactic fact to the
restricted machine semantics: two executions that agree on the registers
currently marked defined continue to agree on every newly defined register.
-/

import NaryaFormal.X86Refinement
import NaryaFormal.X86Dataflow

namespace NaryaFormal.X86

/-- Equality in one SIMD lane, restricted to the currently defined ZMM set. -/
def laneEquivalentOn {Other : Type} (defined : DefinedRegisters)
    (lane : Fin 8) (left right : MachineState Other) : Prop :=
  left.mem = right.mem ∧
    ∀ register, defined register = true →
      left.zmm register lane = right.zmm register lane

theorem laneEquivalentOn_write {Other : Type} (defined : DefinedRegisters)
    (lane : Fin 8) (left right : MachineState Other) (target : ZReg)
    (leftValue rightValue : Zmm)
    (hequivalent : laneEquivalentOn defined lane left right)
    (hvalue : leftValue lane = rightValue lane) :
    laneEquivalentOn (defineRegister defined target) lane
      (writeZmm left target leftValue) (writeZmm right target rightValue) := by
  constructor
  · exact hequivalent.1
  · intro register hdefined
    by_cases htarget : register = target
    · subst register
      simpa [writeZmm, setZmm] using hvalue
    · have hprevious : defined register = true := by
        simpa [defineRegister, htarget] using hdefined
      simpa [writeZmm, setZmm, htarget] using hequivalent.2 register hprevious

/-- Instructions admitted to the decoded register-only arithmetic core. -/
def isCoreInstruction : Instruction → Bool
  | .vpxorq .. | .vpmadd52luq .. | .vpmadd52huq .. | .vpaddq ..
  | .vpmullq .. | .vpandq .. | .vpsllq .. | .vpsrlq ..
  | .vpbroadcastq .. => true
  | _ => false

/--
One decoded core instruction cannot distinguish two selected lanes that agree
on all of its certified dependencies and share the same byte memory.
-/
theorem executeCoreInstruction_noninterference {Other : Type}
    (defined : DefinedRegisters) (lane : Fin 8)
    (instruction : Instruction) (left right rightNext : MachineState Other)
    (hcore : isCoreInstruction instruction = true)
    (hdependencies : dependenciesDefined defined instruction = true)
    (hequivalent : laneEquivalentOn defined lane left right)
    (hright : executeInstruction instruction right = .ok (.next rightNext)) :
    ∃ leftNext,
      executeInstruction instruction left = .ok (.next leftNext) ∧
      laneEquivalentOn (addInstructionWrites defined instruction) lane
        leftNext rightNext := by
  cases instruction with
  | vmovdqu64Load destination base displacement =>
      simp [isCoreInstruction] at hcore
  | vmovdqu64Store base displacement source =>
      simp [isCoreInstruction] at hcore
  | vpxorq destination source1 source2 =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      by_cases hsources : source1 = source2
      · subst source2
        simp [vpxorq, laneMap2, qwordXor]
      · have hdeps : defined source1 = true ∧ defined source2 = true := by
          simpa [dependenciesDefined, instructionDependencies, hsources] using
            hdependencies
        simp [vpxorq, laneMap2, hequivalent.2 source1 hdeps.1,
          hequivalent.2 source2 hdeps.2]
  | vpmadd52luq destination source1 source2 =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined destination = true ∧ defined source1 = true ∧
          defined source2 = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpmadd52luq, laneMap3,
        hequivalent.2 destination hdeps.1,
        hequivalent.2 source1 hdeps.2.1,
        hequivalent.2 source2 hdeps.2.2]
  | vpmadd52huq destination source1 source2 =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined destination = true ∧ defined source1 = true ∧
          defined source2 = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpmadd52huq, laneMap3,
        hequivalent.2 destination hdeps.1,
        hequivalent.2 source1 hdeps.2.1,
        hequivalent.2 source2 hdeps.2.2]
  | vpaddq destination source1 source2 =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined source1 = true ∧ defined source2 = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpaddq, laneMap2, hequivalent.2 source1 hdeps.1,
        hequivalent.2 source2 hdeps.2]
  | vpmullq destination source1 source2 =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined source1 = true ∧ defined source2 = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpmullq, laneMap2, hequivalent.2 source1 hdeps.1,
        hequivalent.2 source2 hdeps.2]
  | vpandq destination source1 source2 =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined source1 = true ∧ defined source2 = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpandq, laneMap2, hequivalent.2 source1 hdeps.1,
        hequivalent.2 source2 hdeps.2]
  | vpsllq destination source amount =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined source = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpsllq, laneMap1, hequivalent.2 source hdeps]
  | vpsrlq destination source amount =>
      simp [executeInstruction] at hright
      subst rightNext
      refine ⟨_, rfl, ?_⟩
      have hdeps : defined source = true := by
        simpa [dependenciesDefined, instructionDependencies] using hdependencies
      apply laneEquivalentOn_write defined lane left right destination _ _
        hequivalent
      simp [vpsrlq, laneMap1, hequivalent.2 source hdeps]
  | vpbroadcastq destination absoluteAddress =>
      by_cases haddress : absoluteAddress < 2 ^ 64
      · by_cases hread : readableBytes right.mem
            (BitVec.ofNat 64 absoluteAddress) 8 = true
        · simp [executeInstruction, execBroadcast, haddress, hread] at hright
          norm_num at haddress
          simp [haddress] at hright
          change Except.ok (Outcome.next (writeZmm right destination
            (broadcastQword
              (loadQwordLE right.mem (BitVec.ofNat 64 absoluteAddress))))) =
              Except.ok (Outcome.next rightNext) at hright
          cases hright
          have hreadLeft : readableBytes left.mem
              (BitVec.ofNat 64 absoluteAddress) 8 = true := by
            simpa [hequivalent.1] using hread
          refine ⟨writeZmm left destination
              (broadcastQword
                (loadQwordLE left.mem (BitVec.ofNat 64 absoluteAddress))), ?_, ?_⟩
          · have haddressPow : absoluteAddress < 2 ^ 64 := by
              norm_num
              exact haddress
            change (execBroadcast left destination absoluteAddress).map
                Outcome.next = _
            rw [executeBroadcast_readable left destination absoluteAddress
              haddressPow hreadLeft]
            rfl
          · apply laneEquivalentOn_write defined lane left right destination _ _
              hequivalent
            simp [broadcastQword, hequivalent.1]
        · have hreadFalse : readableBytes right.mem
              (BitVec.ofNat 64 absoluteAddress) 8 = false :=
            Bool.eq_false_of_not_eq_true hread
          norm_num at haddress
          simp [executeInstruction, execBroadcast, haddress, hreadFalse] at hright
          change Except.error (Fault.readFault (BitVec.ofNat 64 absoluteAddress)) =
            Except.ok (Outcome.next rightNext) at hright
          contradiction
      · norm_num at haddress
        have hnot : ¬absoluteAddress < 18446744073709551616 := by omega
        simp [executeInstruction, execBroadcast, hnot] at hright
        change Except.error
            (Fault.addressOutOfRange (BitVec.ofNat 64 absoluteAddress)) =
          Except.ok (Outcome.next rightNext) at hright
        contradiction
  | vzeroUpper => simp [isCoreInstruction] at hcore
  | ret => simp [isCoreInstruction] at hcore

/-- The generated arithmetic-core list contains only admitted instructions. -/
theorem arithmetic_core_instructions_admitted :
    GeneratedR51InstructionTrace.arithmeticCorePhase.all isCoreInstruction =
      true := by
  native_decide

/--
Lift single-step noninterference over a decoded core phase. The successful
reference execution supplies all memory-read premises for broadcasts; static
dependency propagation supplies the exact register agreement required at each
step.
-/
theorem runCorePhase_noninterference {Other : Type}
    (instructions : List Instruction) (defined after : DefinedRegisters)
    (lane : Fin 8) (left right rightNext : MachineState Other)
    (hcore : instructions.all isCoreInstruction = true)
    (hdefined : propagateDefined instructions defined = some after)
    (hequivalent : laneEquivalentOn defined lane left right)
    (hright : runMachinePhase instructions right = .ok rightNext) :
    ∃ leftNext,
      runMachinePhase instructions left = .ok leftNext ∧
      laneEquivalentOn after lane leftNext rightNext := by
  induction instructions generalizing defined after left right rightNext with
  | nil =>
      simp only [propagateDefined, Option.some.injEq] at hdefined
      subst after
      simp only [runMachinePhase, Except.ok.injEq] at hright
      subst rightNext
      exact ⟨left, rfl, hequivalent⟩
  | cons instruction rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hcore
      rcases hcore with ⟨hinstruction, hrestCore⟩
      simp only [propagateDefined] at hdefined
      by_cases hdeps : dependenciesDefined defined instruction = true
      · simp only [hdeps, ↓reduceIte] at hdefined
        simp only [runMachinePhase] at hright
        cases hstep : executeInstruction instruction right with
        | error fault => simp [hstep] at hright
        | ok outcome =>
            cases outcome with
            | returned returnedState => simp [hstep] at hright
            | next rightStep =>
                simp [hstep] at hright
                rcases executeCoreInstruction_noninterference defined lane
                    instruction left right rightStep hinstruction hdeps
                    hequivalent hstep with
                  ⟨leftStep, hleftStep, hequivalentStep⟩
                rcases ih (addInstructionWrites defined instruction) after
                    leftStep rightStep rightNext hrestCore hdefined
                    hequivalentStep hright with
                  ⟨leftNext, hleftRest, hequivalentNext⟩
                refine ⟨leftNext, ?_, hequivalentNext⟩
                simp [runMachinePhase, hleftStep, hleftRest]
      · have hdepsFalse : dependenciesDefined defined instruction = false :=
          Bool.eq_false_of_not_eq_true hdeps
        simp [hdepsFalse] at hdefined

/-- Replace only registers that are not certified defined with zero vectors. -/
def sanitizeUndefinedZmm {Other : Type} (defined : DefinedRegisters)
    (state : MachineState Other) : MachineState Other :=
  { state with zmm := fun register =>
      if defined register then state.zmm register else fun _ => 0 }

theorem sanitizeUndefined_laneEquivalent {Other : Type}
    (defined : DefinedRegisters) (lane : Fin 8) (state : MachineState Other) :
    laneEquivalentOn defined lane state (sanitizeUndefinedZmm defined state) := by
  constructor
  · rfl
  · intro register hdefined
    simp [sanitizeUndefinedZmm, hdefined]

/-- Partial machine-to-Nat agreement on a certified register set. -/
def laneAgreesOn {Other : Type} (defined : DefinedRegisters) (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState) : Prop :=
  ∀ register, defined register = true →
    (machine.zmm register lane).toNat = shadow.zmm register

theorem sanitizeUndefined_laneAgrees {Other : Type}
    (defined : DefinedRegisters) (lane : Fin 8) (machine : MachineState Other)
    (shadow : NatShadowState)
    (hagrees : laneAgreesOn defined lane machine shadow)
    (hzero : ∀ register, defined register = false → shadow.zmm register = 0) :
    laneAgrees lane (sanitizeUndefinedZmm defined machine) shadow := by
  intro register
  by_cases hdefined : defined register = true
  · simpa [sanitizeUndefinedZmm, hdefined] using hagrees register hdefined
  · have hfalse : defined register = false := Bool.eq_false_of_not_eq_true hdefined
    simp [sanitizeUndefinedZmm, hfalse, hzero register hfalse]

theorem prepared_shadow_zero_above_27 (environment : NatShadowEnvironment)
    (register : ZReg) (hundefined : registersBelow 28 register = false) :
    (preparedNatShadowState environment).zmm register = 0 := by
  fin_cases register <;>
    simp [registersBelow, preparedNatShadowState, preparedNatZmm] at hundefined ⊢

/--
Capstone scratch-register theorem for the exact 94-instruction arithmetic
core. The caller may supply arbitrary values in ZMM28--31. Agreement with the
mathematical inputs is required only for ZMM0--27; the five output lanes are
identical to execution from a sanitized state because every scratch dependency
is defined before use.
-/
theorem run_arithmetic_core_ignores_undefined_scratch {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hconstants : R51ConstantMemory machine)
    (hagrees : laneAgreesOn (registersBelow 28) lane machine
      (preparedNatShadowState environment)) :
    ∃ next,
      runMachinePhase GeneratedR51InstructionTrace.arithmeticCorePhase machine =
        .ok next ∧
      (next.zmm 10 lane).toNat =
          (normalizedNatShadowState environment).zmm 10 ∧
      (next.zmm 11 lane).toNat =
          (normalizedNatShadowState environment).zmm 11 ∧
      (next.zmm 12 lane).toNat =
          (normalizedNatShadowState environment).zmm 12 ∧
      (next.zmm 13 lane).toNat =
          (normalizedNatShadowState environment).zmm 13 ∧
      (next.zmm 14 lane).toNat =
          (normalizedNatShadowState environment).zmm 14 ∧
      next.mem = machine.mem := by
  let sanitized := sanitizeUndefinedZmm (registersBelow 28) machine
  have hsanitizedAgrees : laneAgrees lane sanitized
      (preparedNatShadowState environment) := by
    exact sanitizeUndefined_laneAgrees (registersBelow 28) lane machine
      (preparedNatShadowState environment) hagrees
      (prepared_shadow_zero_above_27 environment)
  have hsanitizedConstants : R51ConstantMemory sanitized := by
    constructor
    · simpa [sanitized, sanitizeUndefinedZmm] using hconstants.foldReadable
    · simpa [sanitized, sanitizeUndefinedZmm] using hconstants.foldValue
    · simpa [sanitized, sanitizeUndefinedZmm] using hconstants.maskReadable
    · simpa [sanitized, sanitizeUndefinedZmm] using hconstants.maskValue
  rcases run_arithmetic_core_refines environment lane sanitized hx hy
      hsanitizedConstants hsanitizedAgrees with
    ⟨sanitizedNext, hsanitizedRun, hsanitizedResult, hsanitizedMem⟩
  rcases arithmetic_core_defined_outputs with
    ⟨after, hdefined, h10, h11, h12, h13, h14⟩
  rcases runCorePhase_noninterference
      GeneratedR51InstructionTrace.arithmeticCorePhase
      (registersBelow 28) after lane machine sanitized sanitizedNext
      arithmetic_core_instructions_admitted hdefined
      (sanitizeUndefined_laneEquivalent (registersBelow 28) lane machine)
      hsanitizedRun with
    ⟨next, hrun, hequivalent⟩
  refine ⟨next, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hequivalent.2 10 h10, hsanitizedResult 10]
  · rw [hequivalent.2 11 h11, hsanitizedResult 11]
  · rw [hequivalent.2 12 h12, hsanitizedResult 12]
  · rw [hequivalent.2 13 h13, hsanitizedResult 13]
  · rw [hequivalent.2 14 h14, hsanitizedResult 14]
  · exact hequivalent.1.trans (hsanitizedMem.trans rfl)

end NaryaFormal.X86
