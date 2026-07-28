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

/--
The two read-only qwords consumed by the decoded multiplier's broadcast
instructions. Keeping this as an explicit machine-state contract prevents the
proof from silently replacing linked memory with mathematical constants.
-/
structure R51ConstantMemory {Other : Type} (machine : MachineState Other) : Prop where
  foldReadable : readableBytes machine.mem
      (BitVec.ofNat 64 R51Object.ifma_fold19Address) 8 = true
  foldValue : loadQwordLE machine.mem
      (BitVec.ofNat 64 R51Object.ifma_fold19Address) = BitVec.ofNat 64 19
  maskReadable : readableBytes machine.mem
      (BitVec.ofNat 64 R51Object.ifma_mask51Address) 8 = true
  maskValue : loadQwordLE machine.mem
      (BitVec.ofNat 64 R51Object.ifma_mask51Address) =
        BitVec.ofNat 64 (2 ^ 51 - 1)

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

/-- A readable constant broadcast refines the Nat shadow in one SIMD lane. -/
theorem refine_vpbroadcastq {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination : ZReg) (absoluteAddress shadowValue : Nat)
    (haddress : absoluteAddress < 2 ^ 64)
    (hread : readableBytes machine.mem
      (BitVec.ofNat 64 absoluteAddress) 8 = true)
    (hvalue : (loadQwordLE machine.mem
      (BitVec.ofNat 64 absoluteAddress)).toNat = shadowValue)
    (hconstant : shadowConstant absoluteAddress = some shadowValue)
    (hagrees : laneAgrees lane machine shadow) :
    ∃ machineNext shadowNext,
      executeInstruction (.vpbroadcastq destination absoluteAddress) machine =
        .ok (.next machineNext) ∧
      executeNatShadow environment (.vpbroadcastq destination absoluteAddress)
        shadow = some (.next shadowNext) ∧
      laneAgrees lane machineNext shadowNext ∧
      machineNext.mem = machine.mem := by
  let machineNext := writeZmm machine destination
    (broadcastQword
      (loadQwordLE machine.mem (BitVec.ofNat 64 absoluteAddress)))
  let shadowNext := writeNatZmm shadow destination shadowValue
  refine ⟨machineNext, shadowNext, ?_, ?_, ?_, rfl⟩
  · rw [executeInstruction,
      executeBroadcast_readable machine destination absoluteAddress
        haddress hread]
    rfl
  · simp [executeNatShadow, hconstant, shadowNext]
  · apply laneAgrees_write lane machine shadow destination _ _ hagrees
    simp [broadcastQword, hvalue]

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
      laneAgrees lane machineNext shadowNext ∧
      machineNext.mem = machine.mem := by
  cases instruction with
  | vmovdqu64Load destination base displacement =>
      simp [isArithmeticInstruction] at harithmetic
  | vmovdqu64Store base displacement source =>
      simp [isArithmeticInstruction] at harithmetic
  | vpxorq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpxorq lane machine shadow destination source1 source2 hagrees,
        rfl⟩
  | vpmadd52luq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpmadd52luq lane machine shadow destination source1 source2
          hagrees hsafe.1 hsafe.2.1 hsafe.2.2, rfl⟩
  | vpmadd52huq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpmadd52huq lane machine shadow destination source1 source2
          hagrees hsafe.1 hsafe.2.1 hsafe.2.2, rfl⟩
  | vpaddq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpaddq lane machine shadow destination source1 source2
          hagrees hsafe, rfl⟩
  | vpmullq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpmullq lane machine shadow destination source1 source2
          hagrees hsafe, rfl⟩
  | vpandq destination source1 source2 =>
      exact ⟨_, _, rfl, rfl,
        refine_vpandq lane machine shadow destination source1 source2 hagrees,
        rfl⟩
  | vpsllq destination source amount =>
      exact ⟨_, _, rfl, rfl,
        refine_vpsllq lane machine shadow destination source amount
          hagrees hsafe, rfl⟩
  | vpsrlq destination source amount =>
      exact ⟨_, _, rfl, rfl,
        refine_vpsrlq lane machine shadow destination source amount hagrees,
        rfl⟩
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
      laneAgrees lane machineNext shadowNext ∧
      machineNext.mem = machine.mem := by
  induction instructions generalizing machine shadow with
  | nil =>
      exact ⟨machine, shadow, rfl, rfl, hagrees, rfl⟩
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
                ⟨machineStep, shadowStep', hmachine, hshadow', hagrees', hmemStep⟩
              rw [hshadow] at hshadow'
              cases hshadow'
              rcases ih machineStep shadowStep hrest hagrees' with
                ⟨machineNext, shadowNext, hmachineRest, hshadowRest, hnext,
                  hmemRest⟩
              refine ⟨machineNext, shadowNext, ?_, ?_, hnext,
                hmemRest.trans hmemStep⟩
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

theorem lt_u64_of_lt_u61 {value : Nat} (hvalue : value < 2 ^ 61) :
    value < U64 := by
  norm_num [U64] at hvalue ⊢
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
      laneAgrees lane machineNext (productNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  rcases runArithmeticPhase_refines environment lane
      GeneratedR51InstructionTrace.productPhase machine
      (preparedNatShadowState environment)
      (product_phase_machine_safe environment hx hy) hagrees with
    ⟨machineNext, shadowNext, hmachine, hshadow, hagreesNext, hmem⟩
  rw [product_phase_correct environment] at hshadow
  cases hshadow
  exact ⟨machineNext, hmachine, hagreesNext, hmem⟩

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
      laneAgrees lane machineNext (combinedNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  rcases runArithmeticPhase_refines environment lane
      GeneratedR51InstructionTrace.combinePhase machine
      (productNatShadowState environment)
      (combine_phase_machine_safe environment hx hy) hagrees with
    ⟨machineNext, shadowNext, hmachine, hshadow, hagreesNext, hmem⟩
  rw [combine_phase_correct environment] at hshadow
  cases hshadow
  exact ⟨machineNext, hmachine, hagreesNext, hmem⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem fold_arithmetic_phase_machine_safe
    (environment : NatShadowEnvironment)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y) :
    natArithmeticProgramSafe environment
      GeneratedR51InstructionTrace.foldArithmeticPhase
      (foldBroadcastNatShadowState environment) := by
  simp [natArithmeticProgramSafe,
    GeneratedR51InstructionTrace.foldArithmeticPhase,
    GeneratedR51InstructionTrace.foldPhase, executeNatShadow,
    isArithmeticInstruction, natInstructionSafe,
    foldBroadcastNatShadowState, foldBroadcastNatZmm,
    combinedNatZmm, writeNatZmm, setNatZmm]
  obtain ⟨hp5, hp6, hp7, hp8, hp9⟩ :=
    Radix51.AssemblyTrace.fold_products_u64
      environment.x environment.y hx hy
  obtain ⟨hf0, hf1, hf2, hf3, hf4⟩ :=
    Radix51.AssemblyTrace.folded_grouped_u61
      environment.x environment.y hx hy
  exact ⟨by simpa [Nat.mul_comm] using hp5,
    by
      convert lt_u64_of_lt_u61 hf0 using 1
      rw [Radix51.AssemblyTrace.folded_grouped_eq_fold_degrees]
      simp [Radix51.foldDegrees]
      ring,
    by simpa [Nat.mul_comm] using hp6,
    by
      convert lt_u64_of_lt_u61 hf1 using 1
      rw [Radix51.AssemblyTrace.folded_grouped_eq_fold_degrees]
      simp [Radix51.foldDegrees]
      ring,
    by simpa [Nat.mul_comm] using hp7,
    by
      convert lt_u64_of_lt_u61 hf2 using 1
      rw [Radix51.AssemblyTrace.folded_grouped_eq_fold_degrees]
      simp [Radix51.foldDegrees]
      ring,
    by simpa [Nat.mul_comm] using hp8,
    by
      convert lt_u64_of_lt_u61 hf3 using 1
      rw [Radix51.AssemblyTrace.folded_grouped_eq_fold_degrees]
      simp [Radix51.foldDegrees]
      ring,
    by simpa [Nat.mul_comm] using hp9,
    by
      convert lt_u64_of_lt_u61 hf4 using 1
      rw [Radix51.AssemblyTrace.folded_grouped_eq_fold_degrees]
      simp [Radix51.foldDegrees]
      ring⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem normalize_arithmetic_phase_machine_safe
    (environment : NatShadowEnvironment)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y) :
    natArithmeticProgramSafe environment
      GeneratedR51InstructionTrace.normalizeArithmeticPhase
      (normalizeBroadcastNatShadowState environment) := by
  simp [natArithmeticProgramSafe,
    GeneratedR51InstructionTrace.normalizeArithmeticPhase,
    GeneratedR51InstructionTrace.normalizePhase, executeNatShadow,
    isArithmeticInstruction, natInstructionSafe,
    normalizeBroadcastNatShadowState, normalizeBroadcastNatZmm,
    foldedNatZmm, writeNatZmm, setNatZmm, and_mask51_eq_mod]
  obtain ⟨_, ho0, ho1, ho2, ho3, ho4⟩ :=
    Radix51.AssemblyTrace.radix51_mul_assembly_trace_correct
      environment.x environment.y hx hy
  obtain ⟨_, _, _, _, hf4⟩ :=
    Radix51.AssemblyTrace.folded_grouped_u61
      environment.x environment.y hx hy
  have ho0' :
      (Radix51.GeneratedR51MulTrace.assemblyOutput
        environment.x environment.y).l0 < U52 := by
    simpa [Radix51.U52, U52] using ho0
  have ho1' :
      (Radix51.GeneratedR51MulTrace.assemblyOutput
        environment.x environment.y).l1 < U52 := by
    simpa [Radix51.U52, U52] using ho1
  have ho2' :
      (Radix51.GeneratedR51MulTrace.assemblyOutput
        environment.x environment.y).l2 < U52 := by
    simpa [Radix51.U52, U52] using ho2
  have ho3' :
      (Radix51.GeneratedR51MulTrace.assemblyOutput
        environment.x environment.y).l3 < U52 := by
    simpa [Radix51.U52, U52] using ho3
  have ho4' :
      (Radix51.GeneratedR51MulTrace.assemblyOutput
        environment.x environment.y).l4 < U52 := by
    simpa [Radix51.U52, U52] using ho4
  have hcarry :
      Radix51.GeneratedR51MulTrace.traceCarry
        (Radix51.GeneratedR51MulTrace.foldedGrouped
          environment.x environment.y).l4 < U52 := by
    have hc := Radix51.carry_lt_1024_of_u61 hf4
    norm_num [Radix51.GeneratedR51MulTrace.traceCarry,
      Radix51.carry, Radix51.B, U52] at hc ⊢
    omega
  exact ⟨by
      simpa [Radix51.GeneratedR51MulTrace.assemblyOutput,
        Radix51.GeneratedR51MulTrace.traceRemainder,
        Radix51.GeneratedR51MulTrace.traceCarry,
        Radix51.GeneratedR51MulTrace.foldConstant] using
          lt_u64_of_lt_u52 ho1',
    by
      simpa [Radix51.GeneratedR51MulTrace.assemblyOutput,
        Radix51.GeneratedR51MulTrace.traceRemainder,
        Radix51.GeneratedR51MulTrace.traceCarry,
        Radix51.GeneratedR51MulTrace.foldConstant] using
          lt_u64_of_lt_u52 ho2',
    by
      simpa [Radix51.GeneratedR51MulTrace.assemblyOutput,
        Radix51.GeneratedR51MulTrace.traceRemainder,
        Radix51.GeneratedR51MulTrace.traceCarry,
        Radix51.GeneratedR51MulTrace.foldConstant] using
          lt_u64_of_lt_u52 ho3',
    by
      simpa [Radix51.GeneratedR51MulTrace.assemblyOutput,
        Radix51.GeneratedR51MulTrace.traceRemainder,
        Radix51.GeneratedR51MulTrace.traceCarry,
        Radix51.GeneratedR51MulTrace.foldConstant] using
          lt_u64_of_lt_u52 ho4',
    by norm_num [U52],
    hcarry,
    by
      simpa [Radix51.GeneratedR51MulTrace.assemblyOutput,
        Radix51.GeneratedR51MulTrace.traceRemainder,
        Radix51.GeneratedR51MulTrace.traceCarry,
        Radix51.GeneratedR51MulTrace.foldConstant] using
          lt_u64_of_lt_u52 ho0'⟩

theorem run_fold_broadcast_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hconstants : R51ConstantMemory machine)
    (hagrees : laneAgrees lane machine
      (combinedNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase GeneratedR51InstructionTrace.foldBroadcastPhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext
        (foldBroadcastNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  have hvalue :
      (loadQwordLE machine.mem
        (BitVec.ofNat 64 R51Object.ifma_fold19Address)).toNat = 19 := by
    rw [hconstants.foldValue]
    norm_num
  have hconstant :
      shadowConstant R51Object.ifma_fold19Address = some 19 := by
    norm_num [shadowConstant, R51Object.ifma_fold19Address,
      R51Object.ifma_mask51Address]
  rcases refine_vpbroadcastq environment lane machine
      (combinedNatShadowState environment) ⟨30, by decide⟩
      R51Object.ifma_fold19Address 19
      (by norm_num [R51Object.ifma_fold19Address])
      hconstants.foldReadable hvalue hconstant hagrees with
    ⟨machineNext, shadowNext, hmachine, hshadow, hagreesNext, hmem⟩
  have hshadowExpected :
      executeNatShadow environment
        (.vpbroadcastq ⟨30, by decide⟩ R51Object.ifma_fold19Address)
        (combinedNatShadowState environment) =
          some (.next (foldBroadcastNatShadowState environment)) := by
    simp [executeNatShadow, hconstant]
    exact fold_broadcast_state_eq environment
  rw [hshadowExpected] at hshadow
  cases hshadow
  refine ⟨machineNext, ?_, hagreesNext, hmem⟩
  have hmachine' :
      executeInstruction
        (.vpbroadcastq (30 : ZReg) R51Object.ifma_fold19Address) machine =
          .ok (.next machineNext) := by
    simpa using hmachine
  simp [GeneratedR51InstructionTrace.foldBroadcastPhase,
    GeneratedR51InstructionTrace.foldPhase, runMachinePhase, hmachine']

theorem run_fold_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hconstants : R51ConstantMemory machine)
    (hagrees : laneAgrees lane machine
      (combinedNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase GeneratedR51InstructionTrace.foldPhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext (foldedNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  rcases run_fold_broadcast_phase_refines environment lane machine
      hconstants hagrees with
    ⟨machineMiddle, hmachineFirst, hagreesMiddle, hmemFirst⟩
  rcases runArithmeticPhase_refines environment lane
      GeneratedR51InstructionTrace.foldArithmeticPhase machineMiddle
      (foldBroadcastNatShadowState environment)
      (fold_arithmetic_phase_machine_safe environment hx hy)
      hagreesMiddle with
    ⟨machineNext, shadowNext, hmachineRest, hshadowRest, hagreesNext,
      hmemRest⟩
  rw [fold_arithmetic_phase_correct environment] at hshadowRest
  cases hshadowRest
  refine ⟨machineNext, ?_, hagreesNext, hmemRest.trans hmemFirst⟩
  rw [GeneratedR51InstructionTrace.constant_phase_splits.1,
    runMachinePhase_append, hmachineFirst]
  exact hmachineRest

theorem run_normalize_broadcast_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hconstants : R51ConstantMemory machine)
    (hagrees : laneAgrees lane machine
      (foldedNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase
        GeneratedR51InstructionTrace.normalizeBroadcastPhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext
        (normalizeBroadcastNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  have hvalue :
      (loadQwordLE machine.mem
        (BitVec.ofNat 64 R51Object.ifma_mask51Address)).toNat =
          2 ^ 51 - 1 := by
    rw [hconstants.maskValue]
    norm_num
  have hconstant :
      shadowConstant R51Object.ifma_mask51Address = some (2 ^ 51 - 1) := by
    norm_num [shadowConstant, R51Object.ifma_fold19Address,
      R51Object.ifma_mask51Address]
  rcases refine_vpbroadcastq environment lane machine
      (foldedNatShadowState environment) ⟨5, by decide⟩
      R51Object.ifma_mask51Address (2 ^ 51 - 1)
      (by norm_num [R51Object.ifma_mask51Address])
      hconstants.maskReadable hvalue hconstant hagrees with
    ⟨machineNext, shadowNext, hmachine, hshadow, hagreesNext, hmem⟩
  have hshadowExpected :
      executeNatShadow environment
        (.vpbroadcastq ⟨5, by decide⟩ R51Object.ifma_mask51Address)
        (foldedNatShadowState environment) =
          some (.next (normalizeBroadcastNatShadowState environment)) := by
    simp [executeNatShadow, hconstant]
    exact normalize_broadcast_state_eq environment
  rw [hshadowExpected] at hshadow
  cases hshadow
  refine ⟨machineNext, ?_, hagreesNext, hmem⟩
  have hmachine' :
      executeInstruction
        (.vpbroadcastq (5 : ZReg) R51Object.ifma_mask51Address) machine =
          .ok (.next machineNext) := by
    simpa using hmachine
  simp [GeneratedR51InstructionTrace.normalizeBroadcastPhase,
    GeneratedR51InstructionTrace.normalizePhase, runMachinePhase, hmachine']

theorem run_normalize_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hconstants : R51ConstantMemory machine)
    (hagrees : laneAgrees lane machine
      (foldedNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase GeneratedR51InstructionTrace.normalizePhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext
        (normalizedNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  rcases run_normalize_broadcast_phase_refines environment lane machine
      hconstants hagrees with
    ⟨machineMiddle, hmachineFirst, hagreesMiddle, hmemFirst⟩
  rcases runArithmeticPhase_refines environment lane
      GeneratedR51InstructionTrace.normalizeArithmeticPhase machineMiddle
      (normalizeBroadcastNatShadowState environment)
      (normalize_arithmetic_phase_machine_safe environment hx hy)
      hagreesMiddle with
    ⟨machineNext, shadowNext, hmachineRest, hshadowRest, hagreesNext,
      hmemRest⟩
  rw [normalize_arithmetic_phase_correct environment] at hshadowRest
  cases hshadowRest
  refine ⟨machineNext, ?_, hagreesNext, hmemRest.trans hmemFirst⟩
  rw [GeneratedR51InstructionTrace.constant_phase_splits.2.1,
    runMachinePhase_append, hmachineFirst]
  exact hmachineRest

/--
The 94 decoded arithmetic instructions, from the first IFMA product through
the final carry fold, refine the independently generated radix-51 output in a
selected lane. The theorem is fault-aware, proves every IFMA source and u64
accumulator premise, reads the linked constants through memory, and records
that this register-only core leaves memory unchanged.
-/
theorem run_arithmetic_core_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (machine : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hconstants : R51ConstantMemory machine)
    (hagrees : laneAgrees lane machine
      (preparedNatShadowState environment)) :
    ∃ machineNext,
      runMachinePhase GeneratedR51InstructionTrace.arithmeticCorePhase machine =
        .ok machineNext ∧
      laneAgrees lane machineNext
        (normalizedNatShadowState environment) ∧
      machineNext.mem = machine.mem := by
  rcases run_product_phase_refines environment lane machine hx hy hagrees with
    ⟨machineProduct, hproduct, hagreesProduct, hmemProduct⟩
  rcases run_combine_phase_refines environment lane machineProduct hx hy
      hagreesProduct with
    ⟨machineCombined, hcombine, hagreesCombined, hmemCombined⟩
  have hconstantsCombined : R51ConstantMemory machineCombined := by
    constructor
    · simpa [hmemCombined, hmemProduct] using hconstants.foldReadable
    · simpa [hmemCombined, hmemProduct] using hconstants.foldValue
    · simpa [hmemCombined, hmemProduct] using hconstants.maskReadable
    · simpa [hmemCombined, hmemProduct] using hconstants.maskValue
  rcases run_fold_phase_refines environment lane machineCombined hx hy
      hconstantsCombined hagreesCombined with
    ⟨machineFolded, hfold, hagreesFolded, hmemFolded⟩
  have hconstantsFolded : R51ConstantMemory machineFolded := by
    constructor
    · simpa [hmemFolded] using hconstantsCombined.foldReadable
    · simpa [hmemFolded] using hconstantsCombined.foldValue
    · simpa [hmemFolded] using hconstantsCombined.maskReadable
    · simpa [hmemFolded] using hconstantsCombined.maskValue
  rcases run_normalize_phase_refines environment lane machineFolded hx hy
      hconstantsFolded hagreesFolded with
    ⟨machineNext, hnormalize, hagreesNext, hmemNormalize⟩
  refine ⟨machineNext, ?_, hagreesNext,
    hmemNormalize.trans
      (hmemFolded.trans (hmemCombined.trans hmemProduct))⟩
  rw [GeneratedR51InstructionTrace.arithmeticCorePhase]
  calc
    runMachinePhase
        (GeneratedR51InstructionTrace.productPhase ++
          (GeneratedR51InstructionTrace.combinePhase ++
            (GeneratedR51InstructionTrace.foldPhase ++
              GeneratedR51InstructionTrace.normalizePhase))) machine =
        runMachinePhase
          (GeneratedR51InstructionTrace.combinePhase ++
            (GeneratedR51InstructionTrace.foldPhase ++
              GeneratedR51InstructionTrace.normalizePhase)) machineProduct := by
            rw [runMachinePhase_append, hproduct]
            rfl
    _ = runMachinePhase
          (GeneratedR51InstructionTrace.foldPhase ++
            GeneratedR51InstructionTrace.normalizePhase) machineCombined := by
            rw [runMachinePhase_append, hcombine]
            rfl
    _ = runMachinePhase GeneratedR51InstructionTrace.normalizePhase
          machineFolded := by
            rw [runMachinePhase_append, hfold]
            rfl
    _ = .ok machineNext := hnormalize

end NaryaFormal.X86
