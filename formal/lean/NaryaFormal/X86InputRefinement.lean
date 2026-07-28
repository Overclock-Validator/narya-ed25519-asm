/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Input-memory refinement for the exact ten-load and eighteen-clear prefix of
the linked r51 multiplier. The contract is byte-addressed and lane-specific:
each source row must be readable and the selected little-endian qword must
equal the corresponding mathematical limb. No assumption is made about the
caller's incoming ZMM register contents.
-/

import NaryaFormal.X86Noninterference

namespace NaryaFormal.X86

def inputRowAddress {Other : Type} (state : MachineState Other)
    (base : Gpr) (limb : Fin 5) : Addr :=
  addressAdd (state.gpr base) (64 * limb.val)

structure R51InputMemory {Other : Type} (environment : NatShadowEnvironment)
    (lane : Fin 8) (state : MachineState Other) : Prop where
  xReadable : ∀ limb : Fin 5,
    readableBytes state.mem (inputRowAddress state .rsi limb) 64 = true
  yReadable : ∀ limb : Fin 5,
    readableBytes state.mem (inputRowAddress state .rdx limb) 64 = true
  xValue : ∀ limb : Fin 5,
    (loadZmm state.mem (inputRowAddress state .rsi limb) lane).toNat =
      environment.x limb
  yValue : ∀ limb : Fin 5,
    (loadZmm state.mem (inputRowAddress state .rdx limb) lane).toNat =
      environment.y limb

def loadedR51InputState {Other : Type} (state : MachineState Other) :
    MachineState Other :=
  let s0 := vmovdqu64Load state 0 (addressAdd (state.gpr .rsi) 0)
  let s1 := vmovdqu64Load s0 1 (addressAdd (state.gpr .rsi) 64)
  let s2 := vmovdqu64Load s1 2 (addressAdd (state.gpr .rsi) 128)
  let s3 := vmovdqu64Load s2 3 (addressAdd (state.gpr .rsi) 192)
  let s4 := vmovdqu64Load s3 4 (addressAdd (state.gpr .rsi) 256)
  let s5 := vmovdqu64Load s4 5 (addressAdd (state.gpr .rdx) 0)
  let s6 := vmovdqu64Load s5 6 (addressAdd (state.gpr .rdx) 64)
  let s7 := vmovdqu64Load s6 7 (addressAdd (state.gpr .rdx) 128)
  let s8 := vmovdqu64Load s7 8 (addressAdd (state.gpr .rdx) 192)
  vmovdqu64Load s8 9 (addressAdd (state.gpr .rdx) 256)

theorem loaded_input_memory_preserved {Other : Type}
    (state : MachineState Other) :
    (loadedR51InputState state).mem = state.mem := by
  rfl

theorem loaded_input_gprs_preserved {Other : Type}
    (state : MachineState Other) :
    (loadedR51InputState state).gpr = state.gpr := by
  rfl

/-- The exact decoded ten-load prefix succeeds under the input contract. -/
theorem run_load_phase {Other : Type} (environment : NatShadowEnvironment)
    (lane : Fin 8) (state : MachineState Other)
    (hinput : R51InputMemory environment lane state) :
    runMachinePhase GeneratedR51InstructionTrace.loadPhase state =
      .ok (loadedR51InputState state) := by
  let s0 := vmovdqu64Load state 0 (addressAdd (state.gpr .rsi) 0)
  let s1 := vmovdqu64Load s0 1 (addressAdd (s0.gpr .rsi) 64)
  let s2 := vmovdqu64Load s1 2 (addressAdd (s1.gpr .rsi) 128)
  let s3 := vmovdqu64Load s2 3 (addressAdd (s2.gpr .rsi) 192)
  let s4 := vmovdqu64Load s3 4 (addressAdd (s3.gpr .rsi) 256)
  let s5 := vmovdqu64Load s4 5 (addressAdd (s4.gpr .rdx) 0)
  let s6 := vmovdqu64Load s5 6 (addressAdd (s5.gpr .rdx) 64)
  let s7 := vmovdqu64Load s6 7 (addressAdd (s6.gpr .rdx) 128)
  let s8 := vmovdqu64Load s7 8 (addressAdd (s7.gpr .rdx) 192)
  let s9 := vmovdqu64Load s8 9 (addressAdd (s8.gpr .rdx) 256)
  have hr0 := hinput.xReadable (0 : Fin 5)
  have hr1 := hinput.xReadable (1 : Fin 5)
  have hr2 := hinput.xReadable (2 : Fin 5)
  have hr3 := hinput.xReadable (3 : Fin 5)
  have hr4 := hinput.xReadable (4 : Fin 5)
  have hr5 := hinput.yReadable (0 : Fin 5)
  have hr6 := hinput.yReadable (1 : Fin 5)
  have hr7 := hinput.yReadable (2 : Fin 5)
  have hr8 := hinput.yReadable (3 : Fin 5)
  have hr9 := hinput.yReadable (4 : Fin 5)
  norm_num [inputRowAddress] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9
  have he0 : executeInstruction (.vmovdqu64Load 0 .rsi 0) state =
      .ok (.next s0) := by
    change (execVmovdqu64Load state 0 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable state 0 _ hr0]
    rfl
  have he1 : executeInstruction (.vmovdqu64Load 1 .rsi 64) s0 =
      .ok (.next s1) := by
    change (execVmovdqu64Load s0 1 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s0 1]
    · rfl
    · simpa [s0, vmovdqu64Load] using hr1
  have he2 : executeInstruction (.vmovdqu64Load 2 .rsi 128) s1 =
      .ok (.next s2) := by
    change (execVmovdqu64Load s1 2 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s1 2]
    · rfl
    · simpa [s1, s0, vmovdqu64Load] using hr2
  have he3 : executeInstruction (.vmovdqu64Load 3 .rsi 192) s2 =
      .ok (.next s3) := by
    change (execVmovdqu64Load s2 3 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s2 3]
    · rfl
    · simpa [s2, s1, s0, vmovdqu64Load] using hr3
  have he4 : executeInstruction (.vmovdqu64Load 4 .rsi 256) s3 =
      .ok (.next s4) := by
    change (execVmovdqu64Load s3 4 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s3 4]
    · rfl
    · simpa [s3, s2, s1, s0, vmovdqu64Load] using hr4
  have he5 : executeInstruction (.vmovdqu64Load 5 .rdx 0) s4 =
      .ok (.next s5) := by
    change (execVmovdqu64Load s4 5 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s4 5]
    · rfl
    · simpa [s4, s3, s2, s1, s0, vmovdqu64Load] using hr5
  have he6 : executeInstruction (.vmovdqu64Load 6 .rdx 64) s5 =
      .ok (.next s6) := by
    change (execVmovdqu64Load s5 6 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s5 6]
    · rfl
    · simpa [s5, s4, s3, s2, s1, s0, vmovdqu64Load] using hr6
  have he7 : executeInstruction (.vmovdqu64Load 7 .rdx 128) s6 =
      .ok (.next s7) := by
    change (execVmovdqu64Load s6 7 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s6 7]
    · rfl
    · simpa [s6, s5, s4, s3, s2, s1, s0, vmovdqu64Load] using hr7
  have he8 : executeInstruction (.vmovdqu64Load 8 .rdx 192) s7 =
      .ok (.next s8) := by
    change (execVmovdqu64Load s7 8 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s7 8]
    · rfl
    · simpa [s7, s6, s5, s4, s3, s2, s1, s0, vmovdqu64Load] using hr8
  have he9 : executeInstruction (.vmovdqu64Load 9 .rdx 256) s8 =
      .ok (.next s9) := by
    change (execVmovdqu64Load s8 9 _).map Outcome.next = _
    rw [execVmovdqu64Load_readable s8 9]
    · rfl
    · simpa [s8, s7, s6, s5, s4, s3, s2, s1, s0, vmovdqu64Load] using hr9
  simp [GeneratedR51InstructionTrace.loadPhase, runMachinePhase,
    he0, he1, he2, he3, he4, he5, he6, he7, he8, he9]
  rfl

theorem loaded_input_lane_agrees {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (state : MachineState Other) (hinput : R51InputMemory environment lane state) :
    laneAgreesOn (registersBelow 10) lane (loadedR51InputState state)
      (preparedNatShadowState environment) := by
  intro register hdefined
  have hx0 := hinput.xValue (0 : Fin 5)
  have hx1 := hinput.xValue (1 : Fin 5)
  have hx2 := hinput.xValue (2 : Fin 5)
  have hx3 := hinput.xValue (3 : Fin 5)
  have hx4 := hinput.xValue (4 : Fin 5)
  have hy0 := hinput.yValue (0 : Fin 5)
  have hy1 := hinput.yValue (1 : Fin 5)
  have hy2 := hinput.yValue (2 : Fin 5)
  have hy3 := hinput.yValue (3 : Fin 5)
  have hy4 := hinput.yValue (4 : Fin 5)
  fin_cases register <;> norm_num [registersBelow] at hdefined
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hx0
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hx1
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hx2
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hx3
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hx4
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hy0
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hy1
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hy2
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hy3
  · simpa [loadedR51InputState, vmovdqu64Load, setZmm,
      preparedNatShadowState, preparedNatZmm, inputRowAddress] using hy4

def clearTargets : List ZReg :=
  [10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24, 25, 26, 27]

def clearInstruction (target : ZReg) : Instruction :=
  .vpxorq target target target

theorem generated_clear_phase_exact :
    GeneratedR51InstructionTrace.clearPhase = clearTargets.map clearInstruction := by
  native_decide

theorem clear_targets_define_below_28 :
    clearTargets.foldl defineRegister (registersBelow 10) =
      registersBelow 28 := by
  funext register
  fin_cases register <;> decide

theorem prepared_shadow_clear_target_zero (environment : NatShadowEnvironment)
    (target : ZReg) (hmember : target ∈ clearTargets) :
    (preparedNatShadowState environment).zmm target = 0 := by
  fin_cases target <;>
    simp [clearTargets, preparedNatShadowState, preparedNatZmm] at hmember ⊢

theorem laneAgreesOn_clear {Other : Type} (defined : DefinedRegisters)
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other) (target : ZReg)
    (hagrees : laneAgreesOn defined lane machine
      (preparedNatShadowState environment))
    (hzero : (preparedNatShadowState environment).zmm target = 0) :
    laneAgreesOn (defineRegister defined target) lane
      (writeZmm machine target (vpxorq (machine.zmm target) (machine.zmm target)))
      (preparedNatShadowState environment) := by
  intro register hdefined
  by_cases htarget : register = target
  · subst register
    simp [writeZmm, setZmm, vpxorq, laneMap2, qwordXor, hzero]
  · have hprevious : defined register = true := by
      simpa [defineRegister, htarget] using hdefined
    simpa [writeZmm, setZmm, htarget] using hagrees register hprevious

theorem run_clear_targets {Other : Type} (targets : List ZReg)
    (defined : DefinedRegisters) (environment : NatShadowEnvironment)
    (lane : Fin 8) (machine : MachineState Other)
    (hagrees : laneAgreesOn defined lane machine
      (preparedNatShadowState environment))
    (hzero : ∀ target ∈ targets,
      (preparedNatShadowState environment).zmm target = 0) :
    ∃ next,
      runMachinePhase (targets.map clearInstruction) machine = .ok next ∧
      laneAgreesOn (targets.foldl defineRegister defined) lane next
        (preparedNatShadowState environment) ∧
      next.mem = machine.mem ∧ next.gpr = machine.gpr := by
  induction targets generalizing defined machine with
  | nil => exact ⟨machine, rfl, hagrees, rfl, rfl⟩
  | cons target rest ih =>
      let step := writeZmm machine target
        (vpxorq (machine.zmm target) (machine.zmm target))
      have hstep : executeInstruction (clearInstruction target) machine =
          .ok (.next step) := by rfl
      have hagreesStep : laneAgreesOn (defineRegister defined target) lane step
          (preparedNatShadowState environment) :=
        laneAgreesOn_clear defined environment lane machine target hagrees
          (hzero target (by simp))
      have hzeroRest : ∀ candidate ∈ rest,
          (preparedNatShadowState environment).zmm candidate = 0 := by
        intro candidate hmember
        exact hzero candidate (by simp [hmember])
      rcases ih (defineRegister defined target) step hagreesStep hzeroRest with
        ⟨next, hrest, hagreesNext, hmem, hgpr⟩
      refine ⟨next, ?_, hagreesNext, hmem.trans rfl, hgpr.trans rfl⟩
      simp [List.map, runMachinePhase, hstep, hrest]

/--
The decoded load/clear prefix establishes exactly the partial relation required
by the scratch-independent arithmetic theorem, from arbitrary incoming ZMMs.
-/
theorem run_prepare_phase {Other : Type} (environment : NatShadowEnvironment)
    (lane : Fin 8) (state : MachineState Other)
    (hinput : R51InputMemory environment lane state) :
    ∃ next,
      runMachinePhase
          (GeneratedR51InstructionTrace.loadPhase ++
            GeneratedR51InstructionTrace.clearPhase) state = .ok next ∧
      laneAgreesOn (registersBelow 28) lane next
        (preparedNatShadowState environment) ∧
      next.mem = state.mem ∧ next.gpr = state.gpr := by
  have hload := run_load_phase environment lane state hinput
  have hagrees := loaded_input_lane_agrees environment lane state hinput
  rcases run_clear_targets clearTargets (registersBelow 10) environment lane
      (loadedR51InputState state) hagrees
      (prepared_shadow_clear_target_zero environment) with
    ⟨next, hclear, hagreesNext, hmem, hgpr⟩
  refine ⟨next, ?_, ?_, hmem.trans (loaded_input_memory_preserved state),
    hgpr.trans (loaded_input_gprs_preserved state)⟩
  · rw [runMachinePhase_append, hload, generated_clear_phase_exact]
    exact hclear
  · simpa [clear_targets_define_below_28] using hagreesNext

end NaryaFormal.X86
