/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Soundness of the value-parametric transpose executor against the restricted
byte-addressed x86 machine model, and the resulting whole-leaf System V
theorems for the exact projective- and affine-Niels transpose symbols.

`executeSym_sound` is proved once for every instruction form. A new program in
the same instruction subset then needs only kernel evaluation of the symbolic
executor, not a new machine proof.
-/

import NaryaFormal.TransposeX86WholeLeaf
import NaryaFormal.X86MemoryLemmas

namespace NaryaFormal.TransposeWholeX86

open NaryaFormal.X86
open NaryaFormal.Transpose

/-! ### YMM store lemmas -/

/-- Exact read-back of an aligned qword after a 32-byte YMM store into the same
object: the four stored qwords are returned and every other aligned qword is
unchanged. -/
theorem loadQwordLE_storeYmm (memory : Memory) (base : Addr)
    (displacement offset : Nat) (value : Ymm)
    (hdisplacement : displacement % 8 = 0) (hoffset : offset % 8 = 0)
    (hdisplacementBound : displacement + 32 < 2 ^ 64)
    (hoffsetBound : offset + 8 < 2 ^ 64) :
    loadQwordLE (storeYmm memory (addressAdd base displacement) value)
        (addressAdd base offset) =
      if offset = displacement + 24 then value.q3
      else if offset = displacement + 16 then value.q2
      else if offset = displacement + 8 then value.q1
      else if offset = displacement then value.q0
      else loadQwordLE memory (addressAdd base offset) := by
  simp only [storeYmm, addressAdd_nested, Nat.add_zero]
  split_ifs with h3 h2 h1 h0
  · subst h3
    rw [loadQwordLE_storeQwordLE_same]
  · subst h2
    rw [loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_same]
  · subst h1
    rw [loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_same]
  · subst h0
    rw [loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_same]
  · rw [loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega),
      loadQwordLE_storeQwordLE_offset_disjoint _ _ _ _ _ (by omega) (by omega)]


/-- A 32-byte YMM store at `base+displacement` changes no byte outside
`[base, base+displacement+32)`. -/
theorem storeYmm_byte_outside (memory : Memory) (base : Addr)
    (displacement : Nat) (value : Ymm) (candidate : Addr)
    (houtside : ∀ offset, offset < displacement + 32 →
      candidate ≠ addressAdd base offset) :
    (storeYmm memory (addressAdd base displacement) value).byte candidate =
      memory.byte candidate := by
  apply storeYmm_frame
  simp only [ymmWrittenAddresses, qwordBytes, storeAddresses, addressAdd_nested,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' apply And.intro
  all_goals exact houtside _ (by omega)


theorem maskBit_ofNat (mask qword : Nat) (hqword : qword < 64) :
    maskBit (BitVec.ofNat 64 mask) qword = mask.testBit qword := by
  unfold maskBit
  rw [BitVec.getLsbD_ofNat]
  simp [hqword]


/-! ### Positional naturality of the shuffle network -/

def mapQ4 {α β : Type} (f : α → β) (value : Q4 α) : Q4 β :=
  ⟨f value.q0, f value.q1, f value.q2, f value.q3⟩


theorem mapQ4_unpackLow {α β : Type} (f : α → β) (a b : Q4 α) :
    mapQ4 f (unpackLowQword a b) = unpackLowQword (mapQ4 f a) (mapQ4 f b) := rfl


theorem mapQ4_unpackHigh {α β : Type} (f : α → β) (a b : Q4 α) :
    mapQ4 f (unpackHighQword a b) = unpackHighQword (mapQ4 f a) (mapQ4 f b) := rfl


theorem mapQ4_shuffle {α β : Type} (f : α → β) (immediate : Nat) (a b : Q4 α) :
    mapQ4 f (shuffleI64x2Ymm immediate a b) =
      shuffleI64x2Ymm immediate (mapQ4 f a) (mapQ4 f b) := by
  unfold shuffleI64x2Ymm mapQ4
  cases immediate.testBit 0 <;> cases immediate.testBit 1 <;> rfl


/-! ### Interpretation of symbolic values in an entry machine state -/

variable {Other : Type}

/-- The source object pointer for output lane `lane`: slot `lane` of the
pointer table passed in RSI at entry. -/
def sourcePointer (entry : MachineState Other) (lane : Nat) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsi) (8 * lane))


def interpWord (entry : MachineState Other) : SymWord → QWord
  | .entry register => entry.gpr register
  | .output => entry.gpr .rdi
  | .pointerTable => entry.gpr .rsi
  | .sourcePointer lane => sourcePointer entry lane
  | .constant value => BitVec.ofNat 64 value


def entryYmmQword (entry : MachineState Other) (register lane : Nat) : QWord :=
  if hregister : register < 32 then
    if hlane : lane < 8 then entry.zmm ⟨register, hregister⟩ ⟨lane, hlane⟩
    else BitVec.ofNat 64 0
  else BitVec.ofNat 64 0


def interpCell (entry : MachineState Other) : Cell → QWord
  | .source lane byteOffset =>
      loadQwordLE entry.mem (addressAdd (sourcePointer entry lane) byteOffset)
  | .zero => BitVec.ofNat 64 0
  | .entryYmm register lane => entryYmmQword entry register lane


/-- `address` is not one of the bytes of the output object. -/
def OutsideOutput (environment : SymEnvironment) (entry : MachineState Other)
    (address : Addr) : Prop :=
  ∀ offset, offset < environment.outputBytes →
    address ≠ addressAdd (entry.gpr .rdi) offset


/-- Entry contract of a transpose leaf. Only the exact pointer table, the exact
source objects, and the exact output object carry permissions; the output may
not overlap the table or any source. Sources may overlap one another. -/
structure LeafPre (environment : SymEnvironment) (entry : MachineState Other) :
    Prop where
  outputBound : environment.outputBytes < 2 ^ 64
  tableReadable : readableBytes entry.mem (entry.gpr .rsi) 64 = true
  sourceReadable : ∀ lane, lane < 8 →
    readableBytes entry.mem (sourcePointer entry lane) environment.sourceBytes = true
  outputWritable :
    writableBytes entry.mem (entry.gpr .rdi) environment.outputBytes = true
  tableDisjoint : ∀ offset, offset < 64 →
    OutsideOutput environment entry (addressAdd (entry.gpr .rsi) offset)
  sourceDisjoint : ∀ lane offset, lane < 8 → offset < environment.sourceBytes →
    OutsideOutput environment entry (addressAdd (sourcePointer entry lane) offset)


/-- Simulation relation between the symbolic state and a concrete machine state
reached from `entry`. -/
structure Sim (environment : SymEnvironment) (entry : MachineState Other)
    (sym : SymState) (state : MachineState Other) : Prop where
  gpr : ∀ register, state.gpr register = interpWord entry (sym.gpr register)
  lane : ∀ register lane, sym.gpr register = .sourcePointer lane → lane < 8
  ymm : ∀ register,
    ymmOfZmm (state.zmm register) = mapQ4 (interpCell entry) (sym.ymm register)
  opmask : ∀ register value, sym.opmask register = some value →
    state.opmask register = BitVec.ofNat 64 value
  perm : state.mem.perm = entry.mem.perm
  frame : ∀ address, OutsideOutput environment entry address →
    state.mem.byte address = entry.mem.byte address
  output : ∀ offset cell, sym.output offset = some cell →
    offset % 8 = 0 ∧ offset + 8 ≤ environment.outputBytes ∧
      loadQwordLE state.mem (addressAdd (entry.gpr .rdi) offset) =
        interpCell entry cell
  rflags : state.rflags = entry.rflags
  mxcsr : state.mxcsr = entry.mxcsr
  rip : state.rip = entry.rip
  other : state.other = entry.other


theorem sim_initial (environment : SymEnvironment) (entry : MachineState Other) :
    Sim environment entry initialSymState entry where
  gpr := by
    intro register
    cases register <;> rfl
  lane := by
    intro register lane hlane
    cases register <;> cases hlane
  ymm := by
    intro register
    simp [initialSymState, mapQ4, interpCell, entryYmmQword, ymmOfZmm]
  opmask := by
    intro register value hvalue
    cases hvalue
  perm := rfl
  frame := fun _ _ => rfl
  output := by
    intro offset cell hcell
    cases hcell
  rflags := rfl
  mxcsr := rfl
  rip := rfl
  other := rfl


section Step

variable {environment : SymEnvironment} {entry state : MachineState Other}
  {sym : SymState}

theorem Sim.load_outside (hsim : Sim environment entry sym state) (base : Addr)
    (houtside : ∀ offset, offset < 8 →
      OutsideOutput environment entry (addressAdd base offset)) :
    loadQwordLE state.mem base = loadQwordLE entry.mem base :=
  loadQwordLE_congr _ _ _ (fun offset hoffset =>
    hsim.frame _ (houtside offset hoffset))


theorem Sim.load_source (hpre : LeafPre environment entry)
    (hsim : Sim environment entry sym state) (lane displacement inner : Nat)
    (hlane : lane < 8)
    (hbound : displacement + inner + 8 ≤ environment.sourceBytes) :
    loadQwordLE state.mem
        (addressAdd (addressAdd (sourcePointer entry lane) displacement) inner) =
      interpCell entry (.source lane (displacement + inner)) := by
  rw [addressAdd_nested]
  apply hsim.load_outside
  intro offset hoffset
  rw [addressAdd_nested]
  exact hpre.sourceDisjoint lane _ hlane (by omega)


theorem Sim.setGprStep (hsim : Sim environment entry sym state)
    (target : Gpr) (word : SymWord) (value : QWord) (next : SymState)
    (hgpr : next.gpr = setSymGpr sym.gpr target word)
    (hymm : next.ymm = sym.ymm) (hopmask : next.opmask = sym.opmask)
    (houtput : next.output = sym.output)
    (hvalue : value = interpWord entry word)
    (hlane : ∀ lane, word = .sourcePointer lane → lane < 8) :
    Sim environment entry next (writeGpr state target value) where
  gpr := by
    intro register
    rw [hgpr]
    by_cases htarget : register = target
    · simp [writeGpr, setGpr, setSymGpr, htarget, hvalue]
    · simp [writeGpr, setGpr, setSymGpr, htarget, hsim.gpr register]
  lane := by
    intro register lane hword
    rw [hgpr] at hword
    by_cases htarget : register = target
    · simp only [setSymGpr, htarget, if_true] at hword
      exact hlane lane hword
    · simp only [setSymGpr, htarget, if_false] at hword
      exact hsim.lane register lane hword
  ymm := by rw [hymm]; exact hsim.ymm
  opmask := by rw [hopmask]; exact hsim.opmask
  perm := hsim.perm
  frame := hsim.frame
  output := by rw [houtput]; exact hsim.output
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other


theorem Sim.setYmmStep (hsim : Sim environment entry sym state)
    (target : ZReg) (cells : Q4 Cell) (value : Ymm) (next : SymState)
    (hgpr : next.gpr = sym.gpr)
    (hymm : next.ymm = setSymYmm sym.ymm target cells)
    (hopmask : next.opmask = sym.opmask) (houtput : next.output = sym.output)
    (hvalue : value = mapQ4 (interpCell entry) cells) :
    Sim environment entry next (writeYmm state target value) where
  gpr := by rw [hgpr]; exact hsim.gpr
  lane := by rw [hgpr]; exact hsim.lane
  ymm := by
    intro register
    rw [hymm]
    by_cases htarget : register = target
    · simp [writeYmm, setZmm, setSymYmm, htarget, ymmOfZmm_zmmOfYmm, hvalue]
    · simp [writeYmm, setZmm, setSymYmm, htarget, hsim.ymm register]
  opmask := by rw [hopmask]; exact hsim.opmask
  perm := hsim.perm
  frame := hsim.frame
  output := by rw [houtput]; exact hsim.output
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other


theorem Sim.setKRegStep (hsim : Sim environment entry sym state)
    (target : KReg) (maskValue : Nat) (value : QWord) (next : SymState)
    (hgpr : next.gpr = sym.gpr) (hymm : next.ymm = sym.ymm)
    (hopmask : next.opmask = setSymMask sym.opmask target (some maskValue))
    (houtput : next.output = sym.output)
    (hvalue : value = BitVec.ofNat 64 maskValue) :
    Sim environment entry next (writeKReg state target value) where
  gpr := by rw [hgpr]; exact hsim.gpr
  lane := by rw [hgpr]; exact hsim.lane
  ymm := by rw [hymm]; exact hsim.ymm
  opmask := by
    intro register candidate hcandidate
    rw [hopmask] at hcandidate
    by_cases htarget : register = target
    · simp only [setSymMask, htarget, if_true, Option.some.injEq] at hcandidate
      simp [writeKReg, setKReg, htarget, hvalue, hcandidate]
    · simp only [setSymMask] at hcandidate
      rw [if_neg htarget] at hcandidate
      simp [writeKReg, setKReg, htarget, hsim.opmask register candidate hcandidate]
  perm := hsim.perm
  frame := hsim.frame
  output := by rw [houtput]; exact hsim.output
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other


theorem Sim.storeStep (hpre : LeafPre environment entry)
    (hsim : Sim environment entry sym state)
    (displacement : Nat) (source : ZReg)
    (hdisplacement : displacement % 8 = 0)
    (hbound : displacement + 32 ≤ environment.outputBytes) :
    Sim environment entry (symStoreYmm sym displacement (sym.ymm source))
      { state with
        mem := storeYmm state.mem (addressAdd (entry.gpr .rdi) displacement)
          (ymmOfZmm (state.zmm source)) } where
  gpr := hsim.gpr
  lane := hsim.lane
  ymm := hsim.ymm
  opmask := hsim.opmask
  perm := (storeYmm_permissions _ _ _).trans hsim.perm
  frame := by
    intro address houtside
    have hstore := storeYmm_byte_outside state.mem (entry.gpr .rdi) displacement
      (ymmOfZmm (state.zmm source)) address
      (fun offset hoffset => houtside offset (by omega))
    exact hstore.trans (hsim.frame address houtside)
  output := by
    intro offset cell hcell
    have houtputBound := hpre.outputBound
    have hymm := hsim.ymm source
    simp only [symStoreYmm, setSymOutput] at hcell
    split_ifs at hcell with h3 h2 h1 h0
    · cases hcell
      refine ⟨by omega, by omega, ?_⟩
      rw [loadQwordLE_storeYmm _ _ _ _ _ hdisplacement (by omega) (by omega)
        (by omega), if_pos h3, hymm]
      rfl
    · cases hcell
      refine ⟨by omega, by omega, ?_⟩
      rw [loadQwordLE_storeYmm _ _ _ _ _ hdisplacement (by omega) (by omega)
        (by omega), if_neg h3, if_pos h2, hymm]
      rfl
    · cases hcell
      refine ⟨by omega, by omega, ?_⟩
      rw [loadQwordLE_storeYmm _ _ _ _ _ hdisplacement (by omega) (by omega)
        (by omega), if_neg h3, if_neg h2, if_pos h1, hymm]
      rfl
    · cases hcell
      refine ⟨by omega, by omega, ?_⟩
      rw [loadQwordLE_storeYmm _ _ _ _ _ hdisplacement (by omega) (by omega)
        (by omega), if_neg h3, if_neg h2, if_neg h1, if_pos h0, hymm]
      rfl
    · obtain ⟨hmod, hlimit, hload⟩ := hsim.output offset cell hcell
      refine ⟨hmod, hlimit, ?_⟩
      rw [loadQwordLE_storeYmm _ _ _ _ _ hdisplacement hmod (by omega)
        (by omega), if_neg h3, if_neg h2, if_neg h1, if_neg h0]
      exact hload
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other


theorem Sim.vzeroUpperStep (hsim : Sim environment entry sym state) (next : SymState)
    (hgpr : next.gpr = sym.gpr)
    (hymm : next.ymm = fun register => vzeroUpperCells register (sym.ymm register))
    (hopmask : next.opmask = sym.opmask) (houtput : next.output = sym.output) :
    Sim environment entry next (execVzeroUpper state) where
  gpr := by rw [hgpr]; exact hsim.gpr
  lane := by rw [hgpr]; exact hsim.lane
  ymm := by
    intro register
    rw [hymm]
    have hregister := hsim.ymm register
    have h0 := congrArg Q4.q0 hregister
    have h1 := congrArg Q4.q1 hregister
    by_cases hlow : register.val < 16
    · have hthree : ((3 : Fin 8) : Nat) = 3 := rfl
      simp only [mapQ4, ymmOfZmm] at h0 h1
      simp [execVzeroUpper, vzeroUpperRegister, vzeroUpperCells, ymmOfZmm, mapQ4,
        interpCell, hlow, h0, h1, hthree]
    · have hzmm : (execVzeroUpper state).zmm register = state.zmm register := by
        funext lane
        simp [execVzeroUpper, vzeroUpperRegister, hlow]
      rw [hzmm]
      simpa [vzeroUpperCells, hlow] using hregister
  opmask := by rw [hopmask]; exact hsim.opmask
  perm := hsim.perm
  frame := hsim.frame
  output := by rw [houtput]; exact hsim.output
  rflags := hsim.rflags
  mxcsr := hsim.mxcsr
  rip := hsim.rip
  other := hsim.other


/-- Masked-load soundness for one qword. Readability and the source frame are
consulted only when the mask bit is set. -/
theorem Sim.masked_qword (hpre : LeafPre environment entry)
    (hsim : Sim environment entry sym state)
    (lane displacement inner mask qword : Nat) (zeroing : Bool)
    (oldValue : QWord) (oldCell : Cell) (hlane : lane < 8)
    (hold : oldValue = interpCell entry oldCell)
    (hbound : mask.testBit qword = true →
      displacement + inner + 8 ≤ environment.sourceBytes) :
    (if mask.testBit qword then
        loadQwordLE state.mem
          (addressAdd (addressAdd (sourcePointer entry lane) displacement) inner)
      else if zeroing then BitVec.ofNat 64 0 else oldValue) =
      interpCell entry
        (maskedCell lane (displacement + inner) mask qword zeroing oldCell) := by
  unfold maskedCell
  by_cases hbit : mask.testBit qword = true
  · rw [if_pos hbit, if_pos hbit]
    exact hsim.load_source hpre lane displacement inner hlane (hbound hbit)
  · rw [if_neg hbit, if_neg hbit]
    cases zeroing
    · simpa using hold
    · rfl

end Step


/-- Single-step soundness: whenever the symbolic executor accepts a
non-returning instruction, the concrete machine executes it without a fault
and the simulation relation is preserved. -/
theorem executeSym_sound (environment : SymEnvironment)
    (entry : MachineState Other) (hpre : LeafPre environment entry)
    (instruction : Instruction) (sym next : SymState)
    (state : MachineState Other) (hsim : Sim environment entry sym state)
    (hstep : executeSym environment instruction sym = some next) :
    ∃ nextState,
      executeInstruction instruction state = .ok (.next nextState) ∧
        Sim environment entry next nextState := by
  cases instruction with
  | movReg64 destination source =>
      simp only [executeSym, Option.some.injEq] at hstep
      subst hstep
      exact ⟨writeGpr state destination (state.gpr source), rfl,
        hsim.setGprStep destination (sym.gpr source) _ _ rfl rfl rfl rfl
          (hsim.gpr source) (fun lane hlane => hsim.lane source lane hlane)⟩
  | movLoad64 destination base displacement =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i hcondition
        obtain ⟨hbase, hmod, hlimit⟩ := hcondition
        simp only [Option.some.injEq] at hstep
        subst hstep
        have haddress : addressAdd (state.gpr base) displacement =
            addressAdd (entry.gpr .rsi) displacement := by
          rw [hsim.gpr base, hbase]
          rfl
        have hread : readableBytes state.mem
            (addressAdd (state.gpr base) displacement) 8 = true := by
          rw [haddress, readableBytes_of_perm _ _ _ _ hsim.perm]
          exact readableBytes_sub _ _ 64 displacement 8 hpre.tableReadable
            (by omega)
        have hload : loadQwordLE state.mem
            (addressAdd (state.gpr base) displacement) =
              interpWord entry (.sourcePointer (displacement / 8)) := by
          rw [haddress]
          have hslot : 8 * (displacement / 8) = displacement := by omega
          simp only [interpWord, sourcePointer, hslot]
          apply hsim.load_outside
          intro offset hoffset
          rw [addressAdd_nested]
          exact hpre.tableDisjoint _ (by omega)
        refine ⟨writeGpr state destination
          (loadQwordLE state.mem (addressAdd (state.gpr base) displacement)),
          ?_, ?_⟩
        · simp [executeInstruction, hread]
        · exact hsim.setGprStep destination _ _ _ rfl rfl rfl rfl hload
            (fun lane hlane => by
              cases hlane
              omega)
      · cases hstep
  | movImm32 destination value =>
      simp only [executeSym, Option.some.injEq] at hstep
      subst hstep
      exact ⟨writeGpr state destination (BitVec.ofNat 64 (value % 2 ^ 32)), rfl,
        hsim.setGprStep destination (.constant (value % 2 ^ 32)) _ _ rfl rfl rfl rfl
          rfl (fun lane hlane => by cases hlane)⟩
  | kmovb destination source =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i value hword
        simp only [Option.some.injEq] at hstep
        subst hstep
        refine ⟨writeKReg state destination
          (BitVec.ofNat 64 ((state.gpr source).toNat % 2 ^ 8)), rfl, ?_⟩
        refine hsim.setKRegStep destination (value % 2 ^ 8) _
          { sym with
            opmask := setSymMask sym.opmask destination (some (value % 2 ^ 8)) }
          rfl rfl rfl rfl ?_
        rw [hsim.gpr source, hword]
        simp only [interpWord, BitVec.toNat_ofNat]
        congr 1
        exact Nat.mod_mod_of_dvd value (by norm_num)
      · cases hstep
  | ymmLoad destination base displacement =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i sourceLane hword
        split at hstep
        · rename_i hbound
          simp only [Option.some.injEq] at hstep
          subst hstep
          have hlane := hsim.lane base sourceLane hword
          have haddress : addressAdd (state.gpr base) displacement =
              addressAdd (sourcePointer entry sourceLane) displacement := by
            rw [hsim.gpr base, hword]
            rfl
          have hread : readableBytes state.mem
              (addressAdd (state.gpr base) displacement) 32 = true := by
            rw [haddress, readableBytes_of_perm _ _ _ _ hsim.perm]
            exact readableBytes_sub _ _ _ displacement 32
              (hpre.sourceReadable sourceLane hlane) hbound
          refine ⟨writeYmm state destination
            (loadYmm state.mem (addressAdd (state.gpr base) displacement)),
            ?_, ?_⟩
          · simp [executeInstruction, execYmmLoad, hread, Except.map]
          · refine hsim.setYmmStep destination (loadedCells sourceLane displacement)
              _ _ (by rfl) (by rfl) (by rfl) (by rfl) ?_
            rw [haddress]
            have h0 := hsim.load_source hpre sourceLane displacement 0 hlane
              (by omega)
            have h1 := hsim.load_source hpre sourceLane displacement 8 hlane
              (by omega)
            have h2 := hsim.load_source hpre sourceLane displacement 16 hlane
              (by omega)
            have h3 := hsim.load_source hpre sourceLane displacement 24 hlane
              (by omega)
            simp only [Nat.add_zero] at h0
            simp only [loadYmm, loadedCells, mapQ4, h0, h1, h2, h3]
        · cases hstep
      · cases hstep
  | ymmMaskedLoad destination base displacement mask zeroing =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i sourceLane hword
        split at hstep
        · rename_i maskValue hmask
          split at hstep
          · rename_i hbound
            simp only [Option.some.injEq] at hstep
            subst hstep
            obtain ⟨hb0, hb1, hb2, hb3⟩ := hbound
            have hlane := hsim.lane base sourceLane hword
            have haddress : addressAdd (state.gpr base) displacement =
                addressAdd (sourcePointer entry sourceLane) displacement := by
              rw [hsim.gpr base, hword]
              rfl
            have hmaskValue := hsim.opmask mask maskValue hmask
            have hreadable (inner qword : Nat) (hqword : qword < 4)
                (hinner : maskValue.testBit qword = true →
                  displacement + inner + 8 ≤ environment.sourceBytes) :
                (!maskBit (BitVec.ofNat 64 maskValue) qword ||
                  readableBytes state.mem
                    (addressAdd (addressAdd (sourcePointer entry sourceLane)
                      displacement) inner) 8) = true := by
              rw [maskBit_ofNat _ _ (by omega)]
              by_cases hbit : maskValue.testBit qword = true
              · rw [addressAdd_nested, readableBytes_of_perm _ _ _ _ hsim.perm,
                  readableBytes_sub _ _ _ (displacement + inner) 8
                    (hpre.sourceReadable sourceLane hlane) (by
                      have := hinner hbit
                      omega)]
                simp
              · simp [hbit]
            have hread : readableMaskedYmm state.mem
                (addressAdd (state.gpr base) displacement)
                (state.opmask mask) = true := by
              rw [haddress, hmaskValue]
              have hrange : List.range 4 = [0, 1, 2, 3] := by decide
              simp only [readableMaskedYmm, hrange, List.all_cons, List.all_nil,
                Bool.and_true, Bool.and_eq_true]
              exact ⟨hreadable 0 0 (by omega) (by simpa using hb0),
                hreadable 8 1 (by omega) (by simpa using hb1),
                hreadable 16 2 (by omega) (by simpa using hb2),
                hreadable 24 3 (by omega) (by simpa using hb3)⟩
            refine ⟨writeYmm state destination
              (loadMaskedYmm state.mem (addressAdd (state.gpr base) displacement)
                (state.opmask mask) (ymmOfZmm (state.zmm destination)) zeroing),
              ?_, ?_⟩
            · simp [executeInstruction, execYmmMaskedLoad, hread, Except.map]
            · refine hsim.setYmmStep destination
                (maskedCells sourceLane displacement maskValue zeroing
                  (sym.ymm destination)) _ _ (by rfl) (by rfl) (by rfl) (by rfl) ?_
              rw [haddress, hmaskValue]
              have hold := hsim.ymm destination
              have hq0 := hsim.masked_qword hpre sourceLane displacement 0
                maskValue 0 zeroing _ _ hlane (congrArg Q4.q0 hold)
                (by simpa using hb0)
              have hq1 := hsim.masked_qword hpre sourceLane displacement 8
                maskValue 1 zeroing _ _ hlane (congrArg Q4.q1 hold)
                (by simpa using hb1)
              have hq2 := hsim.masked_qword hpre sourceLane displacement 16
                maskValue 2 zeroing _ _ hlane (congrArg Q4.q2 hold)
                (by simpa using hb2)
              have hq3 := hsim.masked_qword hpre sourceLane displacement 24
                maskValue 3 zeroing _ _ hlane (congrArg Q4.q3 hold)
                (by simpa using hb3)
              simp only [Nat.add_zero] at hq0
              simp only [loadMaskedYmm, maskedCells, mapQ4,
                maskBit_ofNat _ _ (by omega : 0 < 64),
                maskBit_ofNat _ _ (by omega : 1 < 64),
                maskBit_ofNat _ _ (by omega : 2 < 64),
                maskBit_ofNat _ _ (by omega : 3 < 64), hq0, hq1, hq2, hq3]
          · cases hstep
        · cases hstep
      · cases hstep
  | ymmStore base displacement source =>
      simp only [executeSym] at hstep
      split at hstep
      · rename_i hcondition
        obtain ⟨hbase, hmod, hbound⟩ := hcondition
        simp only [Option.some.injEq] at hstep
        subst hstep
        have haddress : addressAdd (state.gpr base) displacement =
            addressAdd (entry.gpr .rdi) displacement := by
          rw [hsim.gpr base, hbase]
          rfl
        have hwrite : writableBytes state.mem
            (addressAdd (state.gpr base) displacement) 32 = true := by
          rw [haddress, writableBytes_of_perm _ _ _ _ hsim.perm]
          exact writableBytes_sub _ _ _ displacement 32 hpre.outputWritable hbound
        refine ⟨{ state with
          mem := storeYmm state.mem (addressAdd (state.gpr base) displacement)
            (ymmOfZmm (state.zmm source)) }, ?_, ?_⟩
        · simp [executeInstruction, execYmmStore, hwrite, Except.map]
        · rw [haddress]
          exact hsim.storeStep hpre displacement source hmod hbound
      · cases hstep
  | unpackLow destination source1 source2 =>
      simp only [executeSym, Option.some.injEq] at hstep
      subst hstep
      refine ⟨_, rfl, hsim.setYmmStep destination _ _ _ rfl rfl rfl rfl ?_⟩
      rw [hsim.ymm source1, hsim.ymm source2]
      exact (mapQ4_unpackLow _ _ _).symm
  | unpackHigh destination source1 source2 =>
      simp only [executeSym, Option.some.injEq] at hstep
      subst hstep
      refine ⟨_, rfl, hsim.setYmmStep destination _ _ _ rfl rfl rfl rfl ?_⟩
      rw [hsim.ymm source1, hsim.ymm source2]
      exact (mapQ4_unpackHigh _ _ _).symm
  | shuffleI64x2 destination source1 source2 immediate =>
      simp only [executeSym, Option.some.injEq] at hstep
      subst hstep
      refine ⟨_, rfl, hsim.setYmmStep destination _ _ _ rfl rfl rfl rfl ?_⟩
      rw [hsim.ymm source1, hsim.ymm source2]
      exact (mapQ4_shuffle _ _ _ _).symm
  | vzeroUpper =>
      simp only [executeSym, Option.some.injEq] at hstep
      subst hstep
      exact ⟨execVzeroUpper state, rfl, hsim.vzeroUpperStep _ rfl rfl rfl rfl⟩
  | ret =>
      simp only [executeSym] at hstep
      cases hstep


/-- Whole-body soundness by induction over the program. -/
theorem runSym_sound (environment : SymEnvironment)
    (entry : MachineState Other) (hpre : LeafPre environment entry)
    (program : List Instruction) (sym final : SymState)
    (state : MachineState Other) (hsim : Sim environment entry sym state)
    (hrun : runSym environment program sym = some final) :
    ∃ finalState,
      runPhase program state = .ok finalState ∧
        Sim environment entry final finalState := by
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
          executeSym_sound environment entry hpre instruction sym next state
            hsim hstep
        obtain ⟨finalState, hphase, hfinal⟩ := ih next nextState hnext hrun
        exact ⟨finalState, by simp only [runPhase, hexec, hphase], hfinal⟩
      · cases hrun


/-! ### Return epilogue -/

/-- Exact architectural state after the common `VZEROUPPER; RET` suffix. -/
def epilogueReturnedState (state : MachineState Other) : MachineState Other :=
  let zeroed := execVzeroUpper state
  { zeroed with
    gpr := setGpr zeroed.gpr .rsp (addressAdd (zeroed.gpr .rsp) 8)
    rip := loadQwordLE zeroed.mem (zeroed.gpr .rsp) }


/-- The decoded common epilogue reads the stack return word, advances RSP by
exactly eight, applies the architectural VZEROUPPER effect, and changes no
memory. -/
theorem run_epilogue_readable (state : MachineState Other)
    (hread : readableBytes state.mem (state.gpr .rsp) 8 = true) :
    runProgram Generated.epilogue state =
      .ok (.returned (epilogueReturnedState state)) := by
  simp [Generated.epilogue, runProgram, executeInstruction,
    epilogueReturnedState, execRet, hread, execVzeroUpper]


/-- Machine-level postcondition shared by both transpose leaves, phrased
against the final symbolic state of the non-returning body. -/
structure LeafPost (environment : SymEnvironment) (bodyFinal : SymState)
    (entry final : MachineState Other) : Prop where
  /-- Every symbolically stored qword is read back from the output object. -/
  output : ∀ offset cell, bodyFinal.output offset = some cell →
    loadQwordLE final.mem (addressAdd (entry.gpr .rdi) offset) =
      interpCell entry cell
  /-- No byte outside the output object changed. -/
  frame : ∀ address, OutsideOutput environment entry address →
    final.mem.byte address = entry.mem.byte address
  perm : final.mem.perm = entry.mem.perm
  /-- Normal return: RSP advances by eight and RIP is the entry return word. -/
  rsp : final.gpr .rsp = addressAdd (entry.gpr .rsp) 8
  rip : final.rip = loadQwordLE entry.mem (entry.gpr .rsp)
  /-- Every other GPR holds the interpretation of its symbolic value. -/
  gpr : ∀ register, register ≠ .rsp →
    final.gpr register = interpWord entry (bodyFinal.gpr register)
  rflags : final.rflags = entry.rflags
  mxcsr : final.mxcsr = entry.mxcsr
  other : final.other = entry.other


/-- Generic composition: a symbolically accepted non-returning body followed
by the exact `VZEROUPPER; RET` suffix returns normally and satisfies
`LeafPost`. The return slot must be readable and may not overlap the output
object. -/
theorem run_body_then_epilogue (environment : SymEnvironment)
    (entry : MachineState Other) (hpre : LeafPre environment entry)
    (body : List Instruction) (bodyFinal : SymState)
    (hsym : runSym environment body initialSymState = some bodyFinal)
    (hrsp : bodyFinal.gpr .rsp = .entry .rsp)
    (hstack : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstackDisjoint : ∀ offset, offset < 8 →
      OutsideOutput environment entry (addressAdd (entry.gpr .rsp) offset)) :
    ∃ final,
      runProgram (body ++ Generated.epilogue) entry = .ok (.returned final) ∧
        LeafPost environment bodyFinal entry final := by
  obtain ⟨middle, hphase, hsim⟩ :=
    runSym_sound environment entry hpre body initialSymState bodyFinal entry
      (sim_initial environment entry) hsym
  have hmiddleRsp : middle.gpr .rsp = entry.gpr .rsp := by
    rw [hsim.gpr .rsp, hrsp]
    rfl
  have hread : readableBytes middle.mem (middle.gpr .rsp) 8 = true := by
    rw [hmiddleRsp, readableBytes_of_perm _ _ _ _ hsim.perm]
    exact hstack
  refine ⟨epilogueReturnedState middle, ?_, ?_⟩
  · rw [runProgram_append_of_runPhase _ _ _ _ hphase]
    exact run_epilogue_readable middle hread
  · exact
      { output := fun offset cell hcell => (hsim.output offset cell hcell).2.2
        frame := hsim.frame
        perm := hsim.perm
        rsp := by
          simp [epilogueReturnedState, execVzeroUpper, setGpr, hmiddleRsp]
        rip := by
          simp only [epilogueReturnedState, execVzeroUpper]
          rw [hmiddleRsp]
          exact hsim.load_outside _ hstackDisjoint
        gpr := by
          intro register hregister
          simp [epilogueReturnedState, execVzeroUpper, setGpr, hregister,
            hsim.gpr register]
        rflags := hsim.rflags
        mxcsr := hsim.mxcsr
        other := hsim.other }


/-! ### Whole-leaf capstones -/

/-- Register part of the System V contract: the output pointer is returned in
RAX and every callee-saved GPR is preserved. -/
def ReturnRegisters (entry final : MachineState Other) : Prop :=
  final.gpr .rax = entry.gpr .rdi ∧
  final.gpr .rbx = entry.gpr .rbx ∧
  final.gpr .rbp = entry.gpr .rbp ∧
  final.gpr .r12 = entry.gpr .r12 ∧
  final.gpr .r13 = entry.gpr .r13 ∧
  final.gpr .r14 = entry.gpr .r14 ∧
  final.gpr .r15 = entry.gpr .r15


theorem returnRegisters_of_contract (environment : SymEnvironment)
    (bodyFinal : SymState) (entry final : MachineState Other)
    (hpost : LeafPost environment bodyFinal entry final)
    (hcontract : SymbolicRegisterContract bodyFinal) :
    ReturnRegisters entry final := by
  obtain ⟨hrax, -, hrbx, hrbp, hr12, hr13, hr14, hr15, -⟩ := hcontract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpost.gpr .rax (by decide), hrax]; rfl
  · rw [hpost.gpr .rbx (by decide), hrbx]; rfl
  · rw [hpost.gpr .rbp (by decide), hrbp]; rfl
  · rw [hpost.gpr .r12 (by decide), hr12]; rfl
  · rw [hpost.gpr .r13 (by decide), hr13]; rfl
  · rw [hpost.gpr .r14 (by decide), hr14]; rfl
  · rw [hpost.gpr .r15 (by decide), hr15]; rfl


/-- Whole-leaf machine theorem for the exact projective-Niels transpose symbol.

The committed symbol bytes decode to `Generated.projectiveProgram`. From any
entry state satisfying the leaf contract, that program returns normally, and
for every coordinate, limb, and lane the output qword at
`320*coordinate + 64*limb + 8*lane` equals the entry-memory qword at
`32*limb + 8*coordinate` of the source selected for that lane. No byte outside
the 1280-byte output object changes, permissions are unchanged, RSP advances
by eight, RIP is the entry return word, RAX returns the output pointer, and the
callee-saved GPRs, RFLAGS, MXCSR, and unmodeled state are preserved. -/
theorem projective_whole_leaf_binary_refines (entry : MachineState Other)
    (hpre : LeafPre projectiveEnvironment entry)
    (hstack : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstackDisjoint : ∀ offset, offset < 8 →
      OutsideOutput projectiveEnvironment entry
        (addressAdd (entry.gpr .rsp) offset)) :
    decodeProgram NaryaFormal.TransposeObject.projectiveSymbolBytes =
        some Generated.projectiveProgram ∧
    ∃ final,
      runProgram Generated.projectiveProgram entry = .ok (.returned final) ∧
      (∀ coordinate : Fin 4, ∀ limb : Fin 5, ∀ lane : Fin 8,
        loadQwordLE final.mem
            (addressAdd (entry.gpr .rdi)
              (outputOffset coordinate.val limb.val lane.val)) =
          loadQwordLE entry.mem
            (addressAdd (sourcePointer entry lane.val)
              (32 * limb.val + 8 * coordinate.val))) ∧
      LeafPost projectiveEnvironment projectiveFinal entry final ∧
      ReturnRegisters entry final := by
  refine ⟨projective_whole_symbol_decodes, ?_⟩
  obtain ⟨final, hrun, hpost⟩ :=
    run_body_then_epilogue projectiveEnvironment entry hpre
      Generated.projectiveBody projectiveFinal
      projective_symbolic_execution_succeeds projective_register_contract.2.1
      hstack hstackDisjoint
  refine ⟨final, ?_, ?_, hpost, ?_⟩
  · rw [Generated.projective_program_split]
    exact hrun
  · intro coordinate limb lane
    exact hpost.output _ _ (projective_complete_lane_map coordinate limb lane)
  · exact returnRegisters_of_contract _ _ _ _ hpost projective_register_contract


/-- Whole-leaf machine theorem for the exact affine-Niels transpose symbol.

As `projective_whole_leaf_binary_refines`, for three coordinates and 24-byte
source rows. `LeafPre affineEnvironment` grants read permission to exactly 120
bytes per source object, so the theorem covers a source that ends immediately
before an unreadable page: the masked-off fourth qword of the last row is
never required to be readable. -/
theorem affine_whole_leaf_binary_refines (entry : MachineState Other)
    (hpre : LeafPre affineEnvironment entry)
    (hstack : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstackDisjoint : ∀ offset, offset < 8 →
      OutsideOutput affineEnvironment entry
        (addressAdd (entry.gpr .rsp) offset)) :
    decodeProgram NaryaFormal.TransposeObject.affineSymbolBytes =
        some Generated.affineProgram ∧
    ∃ final,
      runProgram Generated.affineProgram entry = .ok (.returned final) ∧
      (∀ coordinate : Fin 3, ∀ limb : Fin 5, ∀ lane : Fin 8,
        loadQwordLE final.mem
            (addressAdd (entry.gpr .rdi)
              (outputOffset coordinate.val limb.val lane.val)) =
          loadQwordLE entry.mem
            (addressAdd (sourcePointer entry lane.val)
              (24 * limb.val + 8 * coordinate.val))) ∧
      LeafPost affineEnvironment affineFinal entry final ∧
      ReturnRegisters entry final := by
  refine ⟨affine_whole_symbol_decodes, ?_⟩
  obtain ⟨final, hrun, hpost⟩ :=
    run_body_then_epilogue affineEnvironment entry hpre
      Generated.affineBody affineFinal
      affine_symbolic_execution_succeeds affine_register_contract.1.2.1
      hstack hstackDisjoint
  refine ⟨final, ?_, ?_, hpost, ?_⟩
  · rw [Generated.affine_program_split]
    exact hrun
  · intro coordinate limb lane
    exact hpost.output _ _ (affine_complete_lane_map coordinate limb lane)
  · exact returnRegisters_of_contract _ _ _ _ hpost affine_register_contract.1


/-! ### Non-vacuity and fail-closed checks -/

/-- A concrete entry state used only to show the leaf contract is satisfiable:
all-zero memory with every byte readable and writable, the pointer table and
all eight sources at address zero, the output object at `2^20`, and the return
slot at `2^21`. -/
def witnessEntry : MachineState Unit :=
  { gpr := fun register =>
      if register = .rdi then BitVec.ofNat 64 (2 ^ 20)
      else if register = .rsp then BitVec.ofNat 64 (2 ^ 21)
      else BitVec.ofNat 64 0
    zmm := fun _ _ => BitVec.ofNat 64 0
    opmask := fun _ => BitVec.ofNat 64 0
    rflags := BitVec.ofNat 64 0
    mxcsr := BitVec.ofNat 32 0
    mem := { byte := fun _ => BitVec.ofNat 8 0, perm := fun _ => ⟨true, true, false⟩ }
    rip := BitVec.ofNat 64 0
    other := () }


theorem witness_sourcePointer (lane : Nat) :
    sourcePointer witnessEntry lane = BitVec.ofNat 64 0 := by
  simp [sourcePointer, loadQwordLE, witnessEntry]


/-- The hypotheses of both whole-leaf theorems are jointly satisfiable, so
neither theorem holds vacuously. -/
theorem leaf_contract_satisfiable (environment : SymEnvironment)
    (hsource : environment.sourceBytes ≤ 2 ^ 16)
    (houtput : environment.outputBytes ≤ 2 ^ 16) :
    LeafPre environment witnessEntry ∧
      readableBytes witnessEntry.mem (witnessEntry.gpr .rsp) 8 = true ∧
      ∀ offset, offset < 8 →
        OutsideOutput environment witnessEntry
          (addressAdd (witnessEntry.gpr .rsp) offset) := by
  have hrdi : witnessEntry.gpr .rdi = BitVec.ofNat 64 (2 ^ 20) := rfl
  have hrsi : witnessEntry.gpr .rsi = BitVec.ofNat 64 0 := rfl
  have hrsp : witnessEntry.gpr .rsp = BitVec.ofNat 64 (2 ^ 21) := rfl
  refine ⟨?_, ?_, ?_⟩
  · exact
      { outputBound := by omega
        tableReadable := by simp [readableBytes, witnessEntry]
        sourceReadable := by
          intro lane _
          simp [readableBytes, witnessEntry]
        outputWritable := by simp [writableBytes, witnessEntry]
        tableDisjoint := by
          intro offset hoffset inner hinner
          rw [hrdi, hrsi]
          exact addressAdd_ofNat_ne _ _ _ _ (by omega) (by omega) (by omega)
        sourceDisjoint := by
          intro lane offset _ hoffset inner hinner
          rw [hrdi, witness_sourcePointer]
          exact addressAdd_ofNat_ne _ _ _ _ (by omega) (by omega) (by omega) }
  · simp [readableBytes, witnessEntry]
  · intro offset hoffset inner hinner
    rw [hrdi, hrsp]
    exact addressAdd_ofNat_ne _ _ _ _ (by omega) (by omega) (by omega)


/-- The symbolic executor is fail-closed at the affine guard-page boundary: an
unmasked 32-byte load of the last 24-byte row would touch source offset 120
and is rejected. Only the masked form used by the assembly is accepted. -/
theorem affine_unmasked_tail_load_rejected :
    (runSym affineEnvironment
      [.movLoad64 .rdx .rsi 0, .ymmLoad 0 .rdx 96] initialSymState).isSome =
        false := by
  decide


/-- A masked load is rejected while its opmask register is still unknown. -/
theorem masked_load_with_unknown_opmask_rejected :
    (runSym affineEnvironment
      [.movLoad64 .rdx .rsi 0, .ymmMaskedLoad 0 .rdx 96 1 true]
      initialSymState).isSome = false := by
  decide


/-- A store through anything other than the entry output pointer is rejected. -/
theorem store_through_source_pointer_rejected :
    (runSym projectiveEnvironment
      [.movLoad64 .rdx .rsi 0, .ymmStore .rdx 0 0] initialSymState).isSome =
        false := by
  decide

end NaryaFormal.TransposeWholeX86
