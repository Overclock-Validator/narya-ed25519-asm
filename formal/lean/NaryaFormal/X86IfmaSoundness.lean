/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Soundness of the IFMA symbolic executor against the restricted byte-addressed
x86 machine model.

`executeSym_sound` is proved once for every instruction form. A leaf in this
instruction subset then needs only kernel evaluation of the checker plus a
short arithmetic lemma about the resulting expressions; it needs no new
machine, memory, wraparound, or ABI proof.
-/

import NaryaFormal.X86IfmaSymbolic
import NaryaFormal.X86MemoryLemmas

namespace NaryaFormal.IfmaSym

open NaryaFormal.X86

/-! ### Selected-lane arithmetic with explicit bounds -/

theorem luq_lane (accumulator left right : QWord)
    (accumulatorNat leftNat rightNat accumulatorBound leftBound rightBound : Nat)
    (haccumulator : accumulator.toNat = accumulatorNat)
    (hleft : left.toNat = leftNat) (hright : right.toNat = rightNat)
    (haccumulatorBound : accumulatorNat ≤ accumulatorBound)
    (hleftBound : leftNat ≤ leftBound) (hrightBound : rightNat ≤ rightBound)
    (hleft52 : leftBound < 2 ^ 52) (hright52 : rightBound < 2 ^ 52)
    (hsum : accumulatorBound + min (2 ^ 52 - 1) (leftBound * rightBound) < 2 ^ 64) :
    (vpmadd52luqLane accumulator left right).toNat =
        accumulatorNat + (leftNat * rightNat) % 2 ^ 52 ∧
      accumulatorNat + (leftNat * rightNat) % 2 ^ 52 ≤
        accumulatorBound + min (2 ^ 52 - 1) (leftBound * rightBound) := by
  subst haccumulator hleft hright
  have hproduct : (left.toNat * right.toNat) % 2 ^ 52 ≤
      min (2 ^ 52 - 1) (leftBound * rightBound) := by
    apply le_min
    · have hlt := Nat.mod_lt (left.toNat * right.toNat) (by norm_num : 0 < 2 ^ 52)
      omega
    · exact (Nat.mod_le _ _).trans (Nat.mul_le_mul hleftBound hrightBound)
  have hlow : ifmaLo52 left right = (left.toNat * right.toNat) % 2 ^ 52 :=
    ifmaLo52_eq_of_u52 left right (by unfold U52; omega) (by unfold U52; omega)
  have hbound := Nat.add_le_add haccumulatorBound hproduct
  refine ⟨?_, hbound⟩
  rw [vpmadd52luqLane_toNat_of_noWrap _ _ _ (by
    rw [hlow]
    unfold U64
    exact lt_of_le_of_lt hbound hsum), hlow]


theorem huq_lane (accumulator left right : QWord)
    (accumulatorNat leftNat rightNat accumulatorBound leftBound rightBound : Nat)
    (haccumulator : accumulator.toNat = accumulatorNat)
    (hleft : left.toNat = leftNat) (hright : right.toNat = rightNat)
    (haccumulatorBound : accumulatorNat ≤ accumulatorBound)
    (hleftBound : leftNat ≤ leftBound) (hrightBound : rightNat ≤ rightBound)
    (hleft52 : leftBound < 2 ^ 52) (hright52 : rightBound < 2 ^ 52)
    (hsum : accumulatorBound + leftBound * rightBound / 2 ^ 52 < 2 ^ 64) :
    (vpmadd52huqLane accumulator left right).toNat =
        accumulatorNat + (leftNat * rightNat) / 2 ^ 52 ∧
      accumulatorNat + (leftNat * rightNat) / 2 ^ 52 ≤
        accumulatorBound + leftBound * rightBound / 2 ^ 52 := by
  subst haccumulator hleft hright
  have hproduct : (left.toNat * right.toNat) / 2 ^ 52 ≤
      leftBound * rightBound / 2 ^ 52 :=
    Nat.div_le_div_right (Nat.mul_le_mul hleftBound hrightBound)
  have hhigh : ifmaHi52 left right = (left.toNat * right.toNat) / 2 ^ 52 :=
    ifmaHi52_eq_of_u52 left right (by unfold U52; omega) (by unfold U52; omega)
  have hbound := Nat.add_le_add haccumulatorBound hproduct
  refine ⟨?_, hbound⟩
  rw [vpmadd52huqLane_toNat_of_noWrap _ _ _ (by
    rw [hhigh]
    unfold U64
    exact lt_of_le_of_lt hbound hsum), hhigh]


theorem add_lane (left right : QWord) (leftNat rightNat leftBound rightBound : Nat)
    (hleft : left.toNat = leftNat) (hright : right.toNat = rightNat)
    (hleftBound : leftNat ≤ leftBound) (hrightBound : rightNat ≤ rightBound)
    (hsum : leftBound + rightBound < 2 ^ 64) :
    (qwordAdd left right).toNat = leftNat + rightNat ∧
      leftNat + rightNat ≤ leftBound + rightBound := by
  subst hleft hright
  have hbound := Nat.add_le_add hleftBound hrightBound
  exact ⟨qwordAdd_toNat_of_noWrap _ _ (by
    unfold U64
    exact lt_of_le_of_lt hbound hsum), hbound⟩


theorem mul_lane (left right : QWord) (leftNat rightNat leftBound rightBound : Nat)
    (hleft : left.toNat = leftNat) (hright : right.toNat = rightNat)
    (hleftBound : leftNat ≤ leftBound) (hrightBound : rightNat ≤ rightBound)
    (hproduct : leftBound * rightBound < 2 ^ 64) :
    (qwordMul left right).toNat = leftNat * rightNat ∧
      leftNat * rightNat ≤ leftBound * rightBound := by
  subst hleft hright
  have hbound := Nat.mul_le_mul hleftBound hrightBound
  exact ⟨qwordMul_toNat_of_noWrap _ _ (by
    unfold U64
    exact lt_of_le_of_lt hbound hproduct), hbound⟩


theorem and_lane (operand maskWord : QWord) (operandNat mask bits operandBound : Nat)
    (hoperand : operand.toNat = operandNat) (hmaskWord : maskWord.toNat = mask)
    (hmask : mask + 1 = 2 ^ bits) (hoperandBound : operandNat ≤ operandBound) :
    (qwordAnd operand maskWord).toNat = operandNat % 2 ^ bits ∧
      operandNat % 2 ^ bits ≤ min operandBound mask := by
  subst hoperand
  have hmaskEq : mask = 2 ^ bits - 1 := by omega
  have hlt := Nat.mod_lt operand.toNat (Nat.two_pow_pos bits)
  refine ⟨?_, le_min ((Nat.mod_le _ _).trans hoperandBound) (by omega)⟩
  rw [qwordAnd, BitVec.toNat_and, hmaskWord, hmaskEq,
    Nat.and_two_pow_sub_one_eq_mod]


theorem shiftLeft_lane (operand : QWord) (operandNat operandBound amount : Nat)
    (hoperand : operand.toNat = operandNat)
    (hoperandBound : operandNat ≤ operandBound)
    (hproduct : operandBound * 2 ^ amount < 2 ^ 64) :
    (qwordShiftLeft operand amount).toNat = operandNat * 2 ^ amount ∧
      operandNat * 2 ^ amount ≤ operandBound * 2 ^ amount := by
  subst hoperand
  have hbound := Nat.mul_le_mul_right (2 ^ amount) hoperandBound
  exact ⟨qwordShiftLeft_toNat_of_noWrap _ _ (by
    unfold U64
    exact lt_of_le_of_lt hbound hproduct), hbound⟩


theorem shiftRight_lane (operand : QWord) (operandNat operandBound amount : Nat)
    (hoperand : operand.toNat = operandNat)
    (hoperandBound : operandNat ≤ operandBound) :
    (qwordShiftRight operand amount).toNat = operandNat / 2 ^ amount ∧
      operandNat / 2 ^ amount ≤ operandBound / 2 ^ amount := by
  subst hoperand
  exact ⟨qwordShiftRight_toNat _ _, Nat.div_le_div_right hoperandBound⟩


/-! ### Leaf contract and simulation relation -/

variable {Other : Type}

/-- Selected-lane value of one 64-byte input row in entry memory. This is the
meaning of `Expr.input`. -/
def entryInputs (lane : Fin 8) (entry : MachineState Other) (base : Gpr)
    (displacement : Nat) : Nat :=
  (loadZmm entry.mem (addressAdd (entry.gpr base) displacement) lane).toNat


/-- `address` is not one of the bytes of the output object. -/
def OutsideOutput (spec : LeafSpec) (entry : MachineState Other)
    (address : Addr) : Prop :=
  ∀ offset, offset < spec.outputBytes →
    address ≠ addressAdd (entry.gpr spec.outputBase) offset


/-- Entry contract of an IFMA leaf for one selected lane. Input rows and the
output object may overlap arbitrarily. -/
structure LeafPre (spec : LeafSpec) (lane : Fin 8) (entry : MachineState Other) :
    Prop where
  outputBound : spec.outputBytes < 2 ^ 64
  inputReadable : ∀ row ∈ spec.inputs,
    readableBytes entry.mem
      (addressAdd (entry.gpr row.base) row.displacement) 64 = true
  inputBound : ∀ row ∈ spec.inputs,
    entryInputs lane entry row.base row.displacement ≤ row.bound
  constantRange : ∀ constant ∈ spec.constants,
    constant.address < 2 ^ 64 ∧ constant.value < 2 ^ 64
  constantReadable : ∀ constant ∈ spec.constants,
    readableBytes entry.mem (BitVec.ofNat 64 constant.address) 8 = true
  constantValue : ∀ constant ∈ spec.constants,
    loadQwordLE entry.mem (BitVec.ofNat 64 constant.address) =
      BitVec.ofNat 64 constant.value
  outputWritable :
    writableBytes entry.mem (entry.gpr spec.outputBase) spec.outputBytes = true


/-- A symbolic value describes a machine qword: equal as a natural number and
within the tracked bound. -/
def Describes (lane : Fin 8) (entry : MachineState Other) (value : SymVal)
    (word : QWord) : Prop :=
  word.toNat = value.expr.eval (entryInputs lane entry) ∧
    value.expr.eval (entryInputs lane entry) ≤ value.bound


structure Sim (spec : LeafSpec) (lane : Fin 8) (entry : MachineState Other)
    (sym : SymState) (state : MachineState Other) : Prop where
  gpr : state.gpr = entry.gpr
  zmm : ∀ register value, sym.zmm register = some value →
    Describes lane entry value (state.zmm register lane)
  perm : state.mem.perm = entry.mem.perm
  /-- Until the first store, memory is exactly entry memory. -/
  prestore : sym.stored = false → state.mem = entry.mem
  frame : ∀ address, OutsideOutput spec entry address →
    state.mem.byte address = entry.mem.byte address
  output : ∀ displacement value, sym.output displacement = some value →
    displacement % 64 = 0 ∧ displacement + 64 ≤ spec.outputBytes ∧
      Describes lane entry value
        (loadZmm state.mem
          (addressAdd (entry.gpr spec.outputBase) displacement) lane)
  rflags : state.rflags = entry.rflags
  mxcsr : state.mxcsr = entry.mxcsr
  rip : state.rip = entry.rip
  other : state.other = entry.other


theorem sim_initial (spec : LeafSpec) (lane : Fin 8) (entry : MachineState Other) :
    Sim spec lane entry initialSymState entry where
  gpr := rfl
  zmm := by
    intro register value hvalue
    cases hvalue
  perm := rfl
  prestore := fun _ => rfl
  frame := fun _ _ => rfl
  output := by
    intro displacement value hvalue
    cases hvalue
  rflags := rfl
  mxcsr := rfl
  rip := rfl
  other := rfl


section Step

variable {spec : LeafSpec} {lane : Fin 8} {entry state : MachineState Other}
  {sym : SymState}

theorem Sim.writeStep (hsim : Sim spec lane entry sym state) (target : ZReg)
    (machineValue : Zmm) (value : SymVal)
    (hvalue : Describes lane entry value (machineValue lane)) :
    Sim spec lane entry (writeSym sym target value)
      (writeZmm state target machineValue) where
  gpr := hsim.gpr
  zmm := by
    intro register candidate hcandidate
    by_cases htarget : register = target
    · subst htarget
      have hsame : value = candidate := by
        simpa [writeSym, setSymZmm] using hcandidate
      subst hsame
      simpa [writeZmm, setZmm] using hvalue
    · simp only [writeSym, setSymZmm] at hcandidate
      rw [if_neg htarget] at hcandidate
      simpa [writeZmm, setZmm, htarget] using hsim.zmm register candidate hcandidate
  perm := hsim.perm
  prestore := hsim.prestore
  frame := hsim.frame
  output := hsim.output
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other


theorem Sim.storeStep (hpre : LeafPre spec lane entry)
    (hsim : Sim spec lane entry sym state) (displacement : Nat) (source : ZReg)
    (value : SymVal) (hsource : sym.zmm source = some value)
    (hmod : displacement % 64 = 0)
    (hbound : displacement + 64 ≤ spec.outputBytes) :
    Sim spec lane entry
      { sym with
        output := setSymOutput sym.output displacement value
        stored := true }
      { state with
        mem := storeZmm state.mem
          (addressAdd (entry.gpr spec.outputBase) displacement)
          (state.zmm source) } where
  gpr := hsim.gpr
  zmm := hsim.zmm
  perm := (storeZmm_permissions _ _ _).trans hsim.perm
  prestore := by
    intro hstored
    cases hstored
  frame := by
    intro address houtside
    have hstore := storeZmm_byte_outside state.mem (entry.gpr spec.outputBase)
      displacement (state.zmm source) address
      (fun offset hoffset => houtside offset (by omega))
    exact hstore.trans (hsim.frame address houtside)
  output := by
    intro candidate candidateValue hcandidate
    have houtputBound := hpre.outputBound
    simp only [setSymOutput] at hcandidate
    split_ifs at hcandidate with hsame
    · cases hcandidate
      subst hsame
      refine ⟨hmod, hbound, ?_⟩
      rw [loadZmm_storeZmm_same]
      exact hsim.zmm source value hsource
    · obtain ⟨hcandidateMod, hcandidateBound, hcandidateValue⟩ :=
        hsim.output candidate candidateValue hcandidate
      refine ⟨hcandidateMod, hcandidateBound, ?_⟩
      rw [loadZmm_storeZmm_offset_disjoint _ _ _ _ _ (by omega) (by omega)]
      exact hcandidateValue
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other

end Step


/-- Single-step soundness: whenever the checker accepts an instruction, the
concrete machine executes it without a fault and the simulation relation is
preserved. In particular every accepted arithmetic step is free of 64-bit
wraparound and every accepted IFMA operand fits in 52 bits. -/
theorem executeSym_sound (spec : LeafSpec) (lane : Fin 8)
    (entry : MachineState Other) (hpre : LeafPre spec lane entry)
    (instruction : Instruction) (sym next : SymState)
    (state : MachineState Other) (hsim : Sim spec lane entry sym state)
    (hstep : executeSym spec instruction sym = some next) :
    ∃ nextState,
      executeInstruction instruction state = .ok (.next nextState) ∧
        Sim spec lane entry next nextState := by
  cases instruction with
  | vmovdqu64Load destination base displacement =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i hstored
        split at hstep
        · rename_i row hrow
          simp only [Option.some.injEq] at hstep
          subst hstep
          unfold findInput at hrow
          have hmember : row ∈ spec.inputs := List.mem_of_find?_eq_some hrow
          have hmatch := List.find?_some hrow
          simp only [decide_eq_true_eq] at hmatch
          obtain ⟨hbase, hdisplacement⟩ := hmatch
          subst hbase hdisplacement
          have hmem := hsim.prestore hstored
          have hread : readableBytes state.mem
              (addressAdd (state.gpr row.base) row.displacement) 64 = true := by
            rw [hmem, hsim.gpr]
            exact hpre.inputReadable row hmember
          refine ⟨writeZmm state destination
            (loadZmm state.mem
              (addressAdd (state.gpr row.base) row.displacement)), ?_, ?_⟩
          · simp [executeInstruction, execVmovdqu64Load, hread, Except.map,
              vmovdqu64Load, writeZmm]
          · refine hsim.writeStep destination _ _ ⟨?_, ?_⟩
            · rw [hmem, hsim.gpr]
              rfl
            · exact hpre.inputBound row hmember
        · cases hstep
      · cases hstep
  | vmovdqu64Store base displacement source =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i value hvalue
        split at hstep
        · rename_i hcondition
          obtain ⟨hbase, hmod, hbound⟩ := hcondition
          simp only [Option.some.injEq] at hstep
          subst hstep
          subst hbase
          have haddress : addressAdd (state.gpr spec.outputBase) displacement =
              addressAdd (entry.gpr spec.outputBase) displacement := by
            rw [hsim.gpr]
          have hwrite : writableBytes state.mem
              (addressAdd (state.gpr spec.outputBase) displacement) 64 = true := by
            rw [haddress, writableBytes_of_perm _ _ _ _ hsim.perm]
            exact writableBytes_sub _ _ _ displacement 64 hpre.outputWritable
              hbound
          refine ⟨{ state with
            mem := storeZmm state.mem
              (addressAdd (state.gpr spec.outputBase) displacement)
              (state.zmm source) }, ?_, ?_⟩
          · simp [executeInstruction, execVmovdqu64Store, hwrite, Except.map,
              vmovdqu64Store]
          · rw [haddress]
            exact hsim.storeStep hpre displacement source value hvalue hmod hbound
        · cases hstep
      · cases hstep
  | vpxorq destination source1 source2 =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i hsame
        simp only [Option.some.injEq] at hstep
        subst hstep
        subst hsame
        refine ⟨_, rfl, hsim.writeStep destination _ _ ⟨?_, Nat.le_refl _⟩⟩
        simp [vpxorq, laneMap2, qwordXor, Expr.eval]
      · cases hstep
  | vpmadd52luq destination source1 source2 =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i accumulator left right haccumulator hleft hright
        split at hstep
        · rename_i hcondition
          obtain ⟨hleft52, hright52, hsum⟩ := hcondition
          simp only [Option.some.injEq] at hstep
          subst hstep
          obtain ⟨haccumulatorValue, haccumulatorBound⟩ :=
            hsim.zmm destination accumulator haccumulator
          obtain ⟨hleftValue, hleftBound⟩ := hsim.zmm source1 left hleft
          obtain ⟨hrightValue, hrightBound⟩ := hsim.zmm source2 right hright
          exact ⟨_, rfl, hsim.writeStep destination _ _
            (luq_lane _ _ _ _ _ _ _ _ _ haccumulatorValue hleftValue hrightValue
              haccumulatorBound hleftBound hrightBound hleft52 hright52 hsum)⟩
        · cases hstep
      · cases hstep
  | vpmadd52huq destination source1 source2 =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i accumulator left right haccumulator hleft hright
        split at hstep
        · rename_i hcondition
          obtain ⟨hleft52, hright52, hsum⟩ := hcondition
          simp only [Option.some.injEq] at hstep
          subst hstep
          obtain ⟨haccumulatorValue, haccumulatorBound⟩ :=
            hsim.zmm destination accumulator haccumulator
          obtain ⟨hleftValue, hleftBound⟩ := hsim.zmm source1 left hleft
          obtain ⟨hrightValue, hrightBound⟩ := hsim.zmm source2 right hright
          exact ⟨_, rfl, hsim.writeStep destination _ _
            (huq_lane _ _ _ _ _ _ _ _ _ haccumulatorValue hleftValue hrightValue
              haccumulatorBound hleftBound hrightBound hleft52 hright52 hsum)⟩
        · cases hstep
      · cases hstep
  | vpaddq destination source1 source2 =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i left right hleft hright
        split at hstep
        · rename_i hsum
          simp only [Option.some.injEq] at hstep
          subst hstep
          obtain ⟨hleftValue, hleftBound⟩ := hsim.zmm source1 left hleft
          obtain ⟨hrightValue, hrightBound⟩ := hsim.zmm source2 right hright
          exact ⟨_, rfl, hsim.writeStep destination _ _
            (add_lane _ _ _ _ _ _ hleftValue hrightValue hleftBound hrightBound
              hsum)⟩
        · cases hstep
      · cases hstep
  | vpmullq destination source1 source2 =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i left right hleft hright
        split at hstep
        · rename_i hproduct
          simp only [Option.some.injEq] at hstep
          subst hstep
          obtain ⟨hleftValue, hleftBound⟩ := hsim.zmm source1 left hleft
          obtain ⟨hrightValue, hrightBound⟩ := hsim.zmm source2 right hright
          exact ⟨_, rfl, hsim.writeStep destination _ _
            (mul_lane _ _ _ _ _ _ hleftValue hrightValue hleftBound hrightBound
              hproduct)⟩
        · cases hstep
      · cases hstep
  | vpandq destination source1 source2 =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i left mask maskBound hleft hright
        split at hstep
        · rename_i bits hbits
          simp only [Option.some.injEq] at hstep
          subst hstep
          unfold maskBits at hbits
          have hmask := List.find?_some hbits
          simp only [decide_eq_true_eq] at hmask
          obtain ⟨hleftValue, hleftBound⟩ := hsim.zmm source1 left hleft
          obtain ⟨hrightValue, -⟩ := hsim.zmm source2 _ hright
          exact ⟨_, rfl, hsim.writeStep destination _ _
            (and_lane _ _ _ mask _ _ hleftValue hrightValue hmask hleftBound)⟩
        · cases hstep
      · cases hstep
  | vpsllq destination source amount =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i operand hoperand
        split at hstep
        · rename_i hproduct
          simp only [Option.some.injEq] at hstep
          subst hstep
          obtain ⟨hoperandValue, hoperandBound⟩ := hsim.zmm source operand hoperand
          exact ⟨_, rfl, hsim.writeStep destination _ _
            (shiftLeft_lane _ _ _ _ hoperandValue hoperandBound hproduct)⟩
        · cases hstep
      · cases hstep
  | vpsrlq destination source amount =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i operand hoperand
        simp only [Option.some.injEq] at hstep
        subst hstep
        obtain ⟨hoperandValue, hoperandBound⟩ := hsim.zmm source operand hoperand
        exact ⟨_, rfl, hsim.writeStep destination _ _
          (shiftRight_lane _ _ _ _ hoperandValue hoperandBound)⟩
      · cases hstep
  | vpbroadcastq destination absoluteAddress =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i hstored
        split at hstep
        · rename_i constant hconstant
          simp only [Option.some.injEq] at hstep
          subst hstep
          unfold findConstant at hconstant
          have hmember : constant ∈ spec.constants :=
            List.mem_of_find?_eq_some hconstant
          have hmatch := List.find?_some hconstant
          simp only [decide_eq_true_eq] at hmatch
          subst hmatch
          obtain ⟨haddressRange, hvalueRange⟩ := hpre.constantRange constant hmember
          have hmem := hsim.prestore hstored
          have hread : readableBytes state.mem
              (BitVec.ofNat 64 constant.address) 8 = true := by
            rw [hmem]
            exact hpre.constantReadable constant hmember
          refine ⟨writeZmm state destination
            (broadcastQword
              (loadQwordLE state.mem (BitVec.ofNat 64 constant.address))), ?_, ?_⟩
          · simp only [executeInstruction]
            rw [executeBroadcast_readable state destination constant.address
              haddressRange hread]
            rfl
          · refine hsim.writeStep destination _ _ ⟨?_, Nat.le_refl _⟩
            rw [hmem]
            show (loadQwordLE entry.mem
              (BitVec.ofNat 64 constant.address)).toNat = constant.value
            rw [hpre.constantValue constant hmember, BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt hvalueRange
        · cases hstep
      · cases hstep
  | vzeroUpper =>
      simp only [executeSym] at hstep
      cases hstep
  | ret =>
      simp only [executeSym] at hstep
      cases hstep


/-- Whole-body soundness by induction over the program. -/
theorem runSym_sound (spec : LeafSpec) (lane : Fin 8)
    (entry : MachineState Other) (hpre : LeafPre spec lane entry)
    (program : List Instruction) (sym final : SymState)
    (state : MachineState Other) (hsim : Sim spec lane entry sym state)
    (hrun : runSym spec program sym = some final) :
    ∃ finalState,
      runMachinePhase program state = .ok finalState ∧
        Sim spec lane entry final finalState := by
  induction program generalizing sym state with
  | nil =>
      simp only [runSym, Option.some.injEq] at hrun
      subst hrun
      exact ⟨state, rfl, hsim⟩
  | cons instruction rest ih =>
      simp only [runSym] at hrun
      split at hrun
      · rename_i next hstep
        obtain ⟨nextState, hexec, hnext⟩ :=
          executeSym_sound spec lane entry hpre instruction sym next state hsim
            hstep
        obtain ⟨finalState, hphase, hfinal⟩ := ih next nextState hnext hrun
        exact ⟨finalState, by simp only [runMachinePhase, hexec, hphase], hfinal⟩
      · cases hrun


/-! ### Return epilogue and whole-leaf composition -/

def epilogue : List Instruction := [.vzeroUpper, .ret]


/-- Exact architectural state after `VZEROUPPER; RET`. -/
def returnedState (state : MachineState Other) : MachineState Other :=
  { execVzeroUpper state with
    gpr := setGpr state.gpr .rsp (addressAdd (state.gpr .rsp) 8)
    rip := loadQwordLE state.mem (state.gpr .rsp) }


theorem run_epilogue (state : MachineState Other)
    (hreturn : readableBytes state.mem (state.gpr .rsp) 8 = true) :
    runProgram epilogue state = .ok (.returned (returnedState state)) := by
  simp [epilogue, runProgram, executeInstruction, returnedState, execRet,
    hreturn, execVzeroUpper]


/-- Machine-level postcondition of an IFMA leaf, phrased against the final
symbolic state of its non-returning body. -/
structure LeafPost (spec : LeafSpec) (lane : Fin 8) (bodyFinal : SymState)
    (entry final : MachineState Other) : Prop where
  /-- Every stored row holds, in the selected lane, exactly the value of its
  symbolic expression on entry memory, within the tracked bound. -/
  output : ∀ displacement value, bodyFinal.output displacement = some value →
    Describes lane entry value
      (loadZmm final.mem
        (addressAdd (entry.gpr spec.outputBase) displacement) lane)
  /-- No byte outside the output object changed. -/
  frame : ∀ address, OutsideOutput spec entry address →
    final.mem.byte address = entry.mem.byte address
  perm : final.mem.perm = entry.mem.perm
  rsp : final.gpr .rsp = addressAdd (entry.gpr .rsp) 8
  rip : final.rip = loadQwordLE entry.mem (entry.gpr .rsp)
  gpr : ∀ register, register ≠ .rsp → final.gpr register = entry.gpr register
  rflags : final.rflags = entry.rflags
  mxcsr : final.mxcsr = entry.mxcsr
  other : final.other = entry.other


/-- Generic whole-leaf theorem. If the checker accepts `body`, then from any
entry state satisfying the leaf contract, `body` followed by `VZEROUPPER; RET`
returns normally and satisfies `LeafPost`. The return slot must be readable
and may not overlap the output object. -/
theorem run_leaf (spec : LeafSpec) (lane : Fin 8) (entry : MachineState Other)
    (hpre : LeafPre spec lane entry) (body : List Instruction)
    (bodyFinal : SymState)
    (hsym : runSym spec body initialSymState = some bodyFinal)
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput spec entry (addressAdd (entry.gpr .rsp) offset)) :
    ∃ final,
      runProgram (body ++ epilogue) entry = .ok (.returned final) ∧
        LeafPost spec lane bodyFinal entry final := by
  obtain ⟨middle, hphase, hsim⟩ :=
    runSym_sound spec lane entry hpre body initialSymState bodyFinal entry
      (sim_initial spec lane entry) hsym
  have hread : readableBytes middle.mem (middle.gpr .rsp) 8 = true := by
    rw [hsim.gpr, readableBytes_of_perm _ _ _ _ hsim.perm]
    exact hreturn
  refine ⟨returnedState middle, ?_, ?_⟩
  · rw [runProgram_append_of_runMachinePhase _ _ _ _ hphase]
    exact run_epilogue middle hread
  · exact
      { output := fun displacement value hvalue =>
          (hsim.output displacement value hvalue).2.2
        frame := hsim.frame
        perm := hsim.perm
        rsp := by simp [returnedState, setGpr, hsim.gpr]
        rip := by
          simp only [returnedState]
          rw [hsim.gpr]
          exact loadQwordLE_congr _ _ _ (fun offset hoffset =>
            hsim.frame _ (hstack offset hoffset))
        gpr := by
          intro register hregister
          simp [returnedState, setGpr, hregister, hsim.gpr]
        rflags := hsim.rflags
        mxcsr := hsim.mxcsr
        other := hsim.other }

end NaryaFormal.IfmaSym
