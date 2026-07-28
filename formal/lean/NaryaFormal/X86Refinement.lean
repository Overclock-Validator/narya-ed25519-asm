/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Local machine-to-natural refinement lemmas for one SIMD lane. These lemmas
make every no-wrap/u52 premise explicit. The remaining whole-program theorem
must discharge those premises from the source-linked range certificate.
-/

import NaryaFormal.X86NatShadow

namespace NaryaFormal.X86

def laneAgrees {Other : Type} (lane : Fin 8) (machine : MachineState Other)
    (shadow : NatShadowState) : Prop :=
  ∀ register, (machine.zmm register lane).toNat = shadow.zmm register

theorem laneAgrees_write {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (target : ZReg) (machineValue : Zmm) (shadowValue : Nat)
    (hagrees : laneAgrees lane machine shadow)
    (hvalue : (machineValue lane).toNat = shadowValue) :
    laneAgrees lane (writeZmm machine target machineValue)
      (writeNatZmm shadow target shadowValue) := by
  intro register
  by_cases hregister : register = target
  · subst register
    simpa [writeZmm, writeNatZmm, setZmm, setNatZmm] using hvalue
  · simpa [writeZmm, writeNatZmm, setZmm, setNatZmm, hregister]
      using hagrees register

theorem refine_vpxorq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow) :
    laneAgrees lane
      (writeZmm machine destination
        (vpxorq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 ^^^ shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  simp [vpxorq, laneMap2, qwordXor, hagrees source1, hagrees source2]

theorem refine_vpandq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow) :
    laneAgrees lane
      (writeZmm machine destination
        (vpandq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 &&& shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  simp [vpandq, laneMap2, qwordAnd, hagrees source1, hagrees source2]

theorem refine_vpaddq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hnoWrap : shadow.zmm source1 + shadow.zmm source2 < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpaddq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 + shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordAdd (machine.zmm source1 lane)
    (machine.zmm source2 lane)).toNat = _
  rw [qwordAdd_toNat_of_noWrap]
  · rw [hagrees source1, hagrees source2]
  · simpa [hagrees source1, hagrees source2] using hnoWrap

theorem refine_vpmullq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hnoWrap : shadow.zmm source1 * shadow.zmm source2 < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpmullq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 * shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordMul (machine.zmm source1 lane)
    (machine.zmm source2 lane)).toNat = _
  rw [qwordMul_toNat_of_noWrap]
  · rw [hagrees source1, hagrees source2]
  · simpa [hagrees source1, hagrees source2] using hnoWrap

theorem refine_vpsllq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source : ZReg) (amount : Nat)
    (hagrees : laneAgrees lane machine shadow)
    (hnoWrap : shadow.zmm source * 2 ^ amount < U64) :
    laneAgrees lane
      (writeZmm machine destination (vpsllq (machine.zmm source) amount))
      (writeNatZmm shadow destination (shadow.zmm source * 2 ^ amount)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordShiftLeft (machine.zmm source lane) amount).toNat = _
  rw [qwordShiftLeft_toNat_of_noWrap]
  · rw [hagrees source]
  · simpa [hagrees source] using hnoWrap

theorem refine_vpsrlq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source : ZReg) (amount : Nat)
    (hagrees : laneAgrees lane machine shadow) :
    laneAgrees lane
      (writeZmm machine destination (vpsrlq (machine.zmm source) amount))
      (writeNatZmm shadow destination (shadow.zmm source / 2 ^ amount)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordShiftRight (machine.zmm source lane) amount).toNat = _
  rw [qwordShiftRight_toNat, hagrees source]

theorem refine_vpmadd52luq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hsource1 : shadow.zmm source1 < U52)
    (hsource2 : shadow.zmm source2 < U52)
    (hnoWrap : shadow.zmm destination +
      Radix51.lo52 (shadow.zmm source1) (shadow.zmm source2) < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpmadd52luq (machine.zmm destination)
          (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm destination +
          Radix51.lo52 (shadow.zmm source1) (shadow.zmm source2))) := by
  have hm1 : (machine.zmm source1 lane).toNat < U52 := by
    simpa [hagrees source1] using hsource1
  have hm2 : (machine.zmm source2 lane).toNat < U52 := by
    simpa [hagrees source2] using hsource2
  have hlo : ifmaLo52 (machine.zmm source1 lane) (machine.zmm source2 lane) =
      Radix51.lo52 (shadow.zmm source1) (shadow.zmm source2) := by
    rw [ifmaLo52_eq_of_u52 _ _ hm1 hm2]
    simp [Radix51.lo52, Radix51.U52, U52, hagrees source1, hagrees source2]
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (vpmadd52luqLane (machine.zmm destination lane)
    (machine.zmm source1 lane) (machine.zmm source2 lane)).toNat = _
  rw [vpmadd52luqLane_toNat_of_noWrap]
  · rw [hagrees destination, hlo]
  · simpa [hagrees destination, hlo] using hnoWrap

theorem refine_vpmadd52huq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hsource1 : shadow.zmm source1 < U52)
    (hsource2 : shadow.zmm source2 < U52)
    (hnoWrap : shadow.zmm destination +
      Radix51.hi52 (shadow.zmm source1) (shadow.zmm source2) < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpmadd52huq (machine.zmm destination)
          (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm destination +
          Radix51.hi52 (shadow.zmm source1) (shadow.zmm source2))) := by
  have hm1 : (machine.zmm source1 lane).toNat < U52 := by
    simpa [hagrees source1] using hsource1
  have hm2 : (machine.zmm source2 lane).toNat < U52 := by
    simpa [hagrees source2] using hsource2
  have hhi : ifmaHi52 (machine.zmm source1 lane) (machine.zmm source2 lane) =
      Radix51.hi52 (shadow.zmm source1) (shadow.zmm source2) := by
    rw [ifmaHi52_eq_of_u52 _ _ hm1 hm2]
    simp [Radix51.hi52, Radix51.U52, U52, hagrees source1, hagrees source2]
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (vpmadd52huqLane (machine.zmm destination lane)
    (machine.zmm source1 lane) (machine.zmm source2 lane)).toNat = _
  rw [vpmadd52huqLane_toNat_of_noWrap]
  · rw [hagrees destination, hhi]
  · simpa [hagrees destination, hhi] using hnoWrap

/-- The register-only instruction subset used by the arithmetic phases. -/
def isArithmeticInstruction : Instruction → Prop
  | .vpxorq .. | .vpmadd52luq .. | .vpmadd52huq .. | .vpaddq ..
  | .vpmullq .. | .vpandq .. | .vpsllq .. | .vpsrlq .. => True
  | _ => False

/--
Exact premises under which one arithmetic instruction has the same unbounded
natural-number effect as its 64-bit machine execution in a selected lane.
Operations that cannot wrap need no numeric premise.
-/
def natInstructionSafe : Instruction → NatShadowState → Prop
  | .vpmadd52luq destination source1 source2, state =>
      state.zmm source1 < U52 ∧ state.zmm source2 < U52 ∧
        state.zmm destination +
          Radix51.lo52 (state.zmm source1) (state.zmm source2) < U64
  | .vpmadd52huq destination source1 source2, state =>
      state.zmm source1 < U52 ∧ state.zmm source2 < U52 ∧
        state.zmm destination +
          Radix51.hi52 (state.zmm source1) (state.zmm source2) < U64
  | .vpaddq _ source1 source2, state =>
      state.zmm source1 + state.zmm source2 < U64
  | .vpmullq _ source1 source2, state =>
      state.zmm source1 * state.zmm source2 < U64
  | .vpsllq _ source amount, state =>
      state.zmm source * 2 ^ amount < U64
  | _, _ => True

/--
One register-only decoded instruction refines the Nat shadow whenever its
explicit u52/no-wrap certificate holds. Memory operations, broadcasts,
`VZEROUPPER`, and `RET` are deliberately excluded and retain separate ABI
obligations.
-/
theorem executeArithmeticInstruction_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (instruction : Instruction) (machine : MachineState Other)
    (shadow : NatShadowState)
    (harithmetic : isArithmeticInstruction instruction)
    (hsafe : natInstructionSafe instruction shadow)
    (hagrees : laneAgrees lane machine shadow) :
    ∃ machineNext shadowNext,
      executeInstruction instruction machine = .ok (.next machineNext) ∧
      executeNatShadow environment instruction shadow = some (.next shadowNext) ∧
      laneAgrees lane machineNext shadowNext := by
  cases instruction with
  | vmovdqu64Load destination base displacement =>
      simp [isArithmeticInstruction] at harithmetic
  | vmovdqu64Store base displacement source =>
      simp [isArithmeticInstruction] at harithmetic
  | vpxorq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpxorq lane machine shadow destination source1 source2 hagrees⟩
  | vpmadd52luq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpmadd52luq lane machine shadow destination source1 source2
          hagrees hsafe.1 hsafe.2.1 hsafe.2.2⟩
  | vpmadd52huq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpmadd52huq lane machine shadow destination source1 source2
          hagrees hsafe.1 hsafe.2.1 hsafe.2.2⟩
  | vpaddq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpaddq lane machine shadow destination source1 source2
          hagrees hsafe⟩
  | vpmullq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpmullq lane machine shadow destination source1 source2
          hagrees hsafe⟩
  | vpandq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpandq lane machine shadow destination source1 source2 hagrees⟩
  | vpsllq destination source amount =>
      exact ⟨_, _, rfl, rfl,
        refine_vpsllq lane machine shadow destination source amount
          hagrees hsafe⟩
  | vpsrlq destination source amount =>
      exact ⟨_, _, rfl, rfl,
        refine_vpsrlq lane machine shadow destination source amount hagrees⟩
  | vpbroadcastq destination absoluteAddress =>
      simp [isArithmeticInstruction] at harithmetic
  | vzeroUpper =>
      simp [isArithmeticInstruction] at harithmetic
  | ret =>
      simp [isArithmeticInstruction] at harithmetic

/--
A phase certificate records that every decoded instruction is register-only,
that its exact no-wrap premises hold in the state where it executes, and that
the remainder is safe in the resulting shadow state.
-/
def natArithmeticProgramSafe (environment : NatShadowEnvironment) :
    List Instruction → NatShadowState → Prop
  | [], _ => True
  | instruction :: rest, state =>
      match executeNatShadow environment instruction state with
      | some (.next nextState) =>
          isArithmeticInstruction instruction ∧
          natInstructionSafe instruction state ∧
          natArithmeticProgramSafe environment rest nextState
      | _ => False

/--
Compose the local arithmetic lemmas over a certified phase. The resulting
machine and Nat states agree in the selected SIMD lane, while faults or an
unexpected return make the certificate uninhabitable.
-/
theorem runArithmeticPhase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (instructions : List Instruction) (machine : MachineState Other)
    (shadow : NatShadowState)
    (hsafe : natArithmeticProgramSafe environment instructions shadow)
    (hagrees : laneAgrees lane machine shadow) :
    ∃ machineNext shadowNext,
      runMachinePhase instructions machine = .ok machineNext ∧
      runNatPhase environment instructions shadow = some shadowNext ∧
      laneAgrees lane machineNext shadowNext := by
  induction instructions generalizing machine shadow with
  | nil =>
      exact ⟨machine, shadow, rfl, rfl, hagrees⟩
  | cons instruction rest ih =>
      simp only [natArithmeticProgramSafe] at hsafe
      cases hshadow : executeNatShadow environment instruction shadow with
      | none => simp [hshadow] at hsafe
      | some outcome =>
          cases outcome with
          | returned returnState => simp [hshadow] at hsafe
          | next shadowStep =>
              simp [hshadow] at hsafe
              rcases hsafe with ⟨harithmetic, hinstruction, hrest⟩
              rcases executeArithmeticInstruction_refines environment lane
                  instruction machine shadow harithmetic hinstruction hagrees with
                ⟨machineStep, shadowStep', hmachine, hshadow', hagrees'⟩
              rw [hshadow] at hshadow'
              cases hshadow'
              rcases ih machineStep shadowStep hrest hagrees' with
                ⟨machineNext, shadowNext, hmachineRest, hshadowRest, hnext⟩
              refine ⟨machineNext, shadowNext, ?_, ?_, hnext⟩
              · simp [runMachinePhase, hmachine, hmachineRest]
              · simp [runNatPhase, hshadow, hshadowRest]

theorem lt_u64_of_lt_u52 {value : Nat} (hvalue : value < U52) :
    value < U64 := by
  norm_num [U52, U64] at hvalue ⊢
  omega

theorem add2_u64_of_u52 {a b : Nat} (ha : a < U52) (hb : b < U52) :
    a + b < U64 := by
  norm_num [U52, U64] at ha hb ⊢
  omega

theorem add3_u64_of_u52 {a b c : Nat}
    (ha : a < U52) (hb : b < U52) (hc : c < U52) :
    a + b + c < U64 := by
  norm_num [U52, U64] at ha hb hc ⊢
  omega

theorem add4_u64_of_u52 {a b c d : Nat}
    (ha : a < U52) (hb : b < U52) (hc : c < U52) (hd : d < U52) :
    a + b + c + d < U64 := by
  norm_num [U52, U64] at ha hb hc hd ⊢
  omega

theorem add5_u64_of_u52 {a b c d e : Nat}
    (ha : a < U52) (hb : b < U52) (hc : c < U52) (hd : d < U52)
    (he : e < U52) : a + b + c + d + e < U64 := by
  norm_num [U52, U64] at ha hb hc hd he ⊢
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem product_phase_machine_safe (environment : NatShadowEnvironment)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y) :
    natArithmeticProgramSafe environment
      GeneratedR51InstructionTrace.productPhase
      (preparedNatShadowState environment) := by
  simp [natArithmeticProgramSafe, GeneratedR51InstructionTrace.productPhase,
    executeNatShadow, isArithmeticInstruction, natInstructionSafe,
    preparedNatShadowState, preparedNatZmm, writeNatZmm, setNatZmm]
  have hx52 (i : Fin 5) : environment.x i < U52 := by
    simpa [Radix51.U52, U52] using hx i
  have hy52 (i : Fin 5) : environment.y i < U52 := by
    simpa [Radix51.U52, U52] using hy i
  have hlo (i j : Fin 5) :
      Radix51.lo52 (environment.x i) (environment.y j) < U52 :=
    Radix51.lo52_lt _ _
  have hhi (i j : Fin 5) :
      Radix51.hi52 (environment.x i) (environment.y j) < U52 :=
    Radix51.hi52_lt_of_u52 (hx i) (hy j)
  simp [hx52, hy52, hlo, hhi, lt_u64_of_lt_u52, add2_u64_of_u52,
    add3_u64_of_u52, add4_u64_of_u52, add5_u64_of_u52]

theorem run_product_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hagrees : laneAgrees lane machine (preparedNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase GeneratedR51InstructionTrace.productPhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext (productNatShadowState environment) := by
  rcases runArithmeticPhase_refines environment lane
      GeneratedR51InstructionTrace.productPhase machine
      (preparedNatShadowState environment)
      (product_phase_machine_safe environment hx hy) hagrees with
    ⟨machineNext, shadowNext, hmachine, hshadow, hagreesNext⟩
  rw [product_phase_correct environment] at hshadow
  cases hshadow
  exact ⟨machineNext, hmachine, hagreesNext⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem combine_phase_machine_safe (environment : NatShadowEnvironment)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y) :
    natArithmeticProgramSafe environment
      GeneratedR51InstructionTrace.combinePhase
      (productNatShadowState environment) := by
  simp [natArithmeticProgramSafe, GeneratedR51InstructionTrace.combinePhase,
    executeNatShadow, isArithmeticInstruction, natInstructionSafe,
    productNatShadowState, productNatZmm, writeNatZmm, setNatZmm]
  have hs0 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 0) (by norm_num)
  have hs1 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 1) (by norm_num)
  have hs2 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 2) (by norm_num)
  have hs3 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 3) (by norm_num)
  have hs4 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 4) (by norm_num)
  have hs5 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 5) (by norm_num)
  have hs6 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 6) (by norm_num)
  have hs7 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 7) (by norm_num)
  have hs8 := Radix51.AssemblyTrace.high_accumulator_shift_u64
    environment.x environment.y hx hy (degree := 8) (by norm_num)
  have hg1 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 1) (by norm_num)
  have hg2 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 2) (by norm_num)
  have hg3 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 3) (by norm_num)
  have hg4 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 4) (by norm_num)
  have hg5 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 5) (by norm_num)
  have hg6 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 6) (by norm_num)
  have hg7 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 7) (by norm_num)
  have hg8 := Radix51.AssemblyTrace.grouped_degree_u64
    environment.x environment.y hx hy (degree := 8) (by norm_num)
  exact ⟨by simpa [Nat.mul_comm] using hs0,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg1,
    by simpa [Nat.mul_comm] using hs1,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg2,
    by simpa [Nat.mul_comm] using hs2,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg3,
    by simpa [Nat.mul_comm] using hs3,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg4,
    by simpa [Nat.mul_comm] using hs4,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg5,
    by simpa [Nat.mul_comm] using hs5,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg6,
    by simpa [Nat.mul_comm] using hs6,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg7,
    by simpa [Nat.mul_comm] using hs7,
    by simpa [Radix51.GeneratedR51MulTrace.groupedDegree, Nat.mul_comm] using hg8,
    by simpa [Nat.mul_comm] using hs8⟩

theorem run_combine_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hagrees : laneAgrees lane machine (productNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase GeneratedR51InstructionTrace.combinePhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext (combinedNatShadowState environment) := by
  rcases runArithmeticPhase_refines environment lane
      GeneratedR51InstructionTrace.combinePhase machine
      (productNatShadowState environment)
      (combine_phase_machine_safe environment hx hy) hagrees with
    ⟨machineNext, shadowNext, hmachine, hshadow, hagreesNext⟩
  rw [combine_phase_correct environment] at hshadow
  cases hshadow
  exact ⟨machineNext, hmachine, hagreesNext⟩

end NaryaFormal.X86
