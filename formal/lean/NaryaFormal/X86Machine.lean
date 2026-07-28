/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Restricted byte-addressed machine state for the linked r51 multiplier proof.
This models the exact memory layout, vector loads/stores, VZEROUPPER, and RET
effects used by the leaf. Canonical-address checks, CET shadow-stack behavior,
and instruction decoding are separate obligations.
-/

import NaryaFormal.X86VectorSemantics

namespace NaryaFormal.X86

abbrev Addr := BitVec 64
abbrev Byte := BitVec 8
abbrev ZReg := Fin 32
abbrev KReg := Fin 8

inductive Gpr
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

structure Perm where
  read : Bool
  write : Bool
  exec : Bool
deriving DecidableEq, Repr

structure Memory where
  byte : Addr → Byte
  perm : Addr → Perm

structure MachineState (Other : Type) where
  gpr : Gpr → QWord
  zmm : ZReg → Zmm
  opmask : KReg → QWord
  rflags : QWord
  mxcsr : BitVec 32
  mem : Memory
  rip : Addr
  other : Other

inductive Fault
  | badDecode
  | unsupportedEncoding
  /-- A resolved absolute address did not fit in the model's 64-bit address space.
      This is deliberately not a claim about x86-64 canonical-address policy. -/
  | addressOutOfRange (address : Addr)
  | readFault (address : Addr)
  | writeFault (address : Addr)
  | execFault (address : Addr)
  deriving DecidableEq, Repr

inductive Outcome (Other : Type)
  | next (state : MachineState Other)
  | returned (state : MachineState Other)

def addressAdd (base : Addr) (offset : Nat) : Addr :=
  base + BitVec.ofNat 64 offset

theorem addressAdd_nested (base : Addr) (left right : Nat) :
    addressAdd (addressAdd base left) right = addressAdd base (left + right) := by
  simp [addressAdd, BitVec.ofNat_add, BitVec.add_assoc]

def readableBytes (memory : Memory) (base : Addr) (count : Nat) : Bool :=
  (List.range count).all (fun offset => (memory.perm (addressAdd base offset)).read)

def writableBytes (memory : Memory) (base : Addr) (count : Nat) : Bool :=
  (List.range count).all (fun offset => (memory.perm (addressAdd base offset)).write)

def loadQwordLE (memory : Memory) (base : Addr) : QWord :=
  BitVec.ofNat 64
    (∑ offset ∈ Finset.range 8,
      (memory.byte (addressAdd base offset)).toNat * 256 ^ offset)

def qwordByte (word : QWord) (offset : Nat) : Byte :=
  word.extractLsb' (8 * offset) 8

def qwordBytes (word : QWord) : List Byte :=
  [qwordByte word 0, qwordByte word 1, qwordByte word 2, qwordByte word 3,
    qwordByte word 4, qwordByte word 5, qwordByte word 6, qwordByte word 7]

def storeByte (memory : Memory) (address : Addr) (value : Byte) : Memory :=
  { memory with byte := fun candidate => if candidate = address then value else memory.byte candidate }

def storeBytes : Memory → Addr → List Byte → Memory
  | memory, _, [] => memory
  | memory, base, value :: rest =>
      storeBytes (storeByte memory base value) (addressAdd base 1) rest

def storeAddresses : Addr → List Byte → List Addr
  | _, [] => []
  | base, _ :: rest => base :: storeAddresses (addressAdd base 1) rest

def storeQwordLE (memory : Memory) (base : Addr) (word : QWord) : Memory :=
  storeBytes memory base (qwordBytes word)

def loadZmm (memory : Memory) (base : Addr) : Zmm :=
  fun lane => loadQwordLE memory (addressAdd base (8 * lane.val))

def storeZmm (memory : Memory) (base : Addr) (value : Zmm) : Memory :=
  let m0 := storeQwordLE memory (addressAdd base 0) (value 0)
  let m1 := storeQwordLE m0 (addressAdd base 8) (value 1)
  let m2 := storeQwordLE m1 (addressAdd base 16) (value 2)
  let m3 := storeQwordLE m2 (addressAdd base 24) (value 3)
  let m4 := storeQwordLE m3 (addressAdd base 32) (value 4)
  let m5 := storeQwordLE m4 (addressAdd base 40) (value 5)
  let m6 := storeQwordLE m5 (addressAdd base 48) (value 6)
  storeQwordLE m6 (addressAdd base 56) (value 7)

def zmmWrittenAddresses (base : Addr) (value : Zmm) : List Addr :=
  storeAddresses (addressAdd base 0) (qwordBytes (value 0)) ++
  storeAddresses (addressAdd base 8) (qwordBytes (value 1)) ++
  storeAddresses (addressAdd base 16) (qwordBytes (value 2)) ++
  storeAddresses (addressAdd base 24) (qwordBytes (value 3)) ++
  storeAddresses (addressAdd base 32) (qwordBytes (value 4)) ++
  storeAddresses (addressAdd base 40) (qwordBytes (value 5)) ++
  storeAddresses (addressAdd base 48) (qwordBytes (value 6)) ++
  storeAddresses (addressAdd base 56) (qwordBytes (value 7))

def setGpr (registers : Gpr → QWord) (target : Gpr) (value : QWord) :
    Gpr → QWord :=
  fun register => if register = target then value else registers register

def setZmm (registers : ZReg → Zmm) (target : ZReg) (value : Zmm) :
    ZReg → Zmm :=
  fun register => if register = target then value else registers register

def vmovdqu64Load {Other : Type} (state : MachineState Other) (target : ZReg)
    (base : Addr) : MachineState Other :=
  { state with zmm := setZmm state.zmm target (loadZmm state.mem base) }

def vmovdqu64Store {Other : Type} (state : MachineState Other) (base : Addr)
    (source : ZReg) : MachineState Other :=
  { state with mem := storeZmm state.mem base (state.zmm source) }

def execVmovdqu64Load {Other : Type} (state : MachineState Other)
    (target : ZReg) (base : Addr) : Except Fault (MachineState Other) :=
  if readableBytes state.mem base 64 then
    .ok (vmovdqu64Load state target base)
  else
    .error (.readFault base)

def execVmovdqu64Store {Other : Type} (state : MachineState Other)
    (base : Addr) (source : ZReg) : Except Fault (MachineState Other) :=
  if writableBytes state.mem base 64 then
    .ok (vmovdqu64Store state base source)
  else
    .error (.writeFault base)

def vzeroUpperRegister (register : ZReg) (value : Zmm) : Zmm :=
  fun lane =>
    if register.val < 16 ∧ 2 ≤ lane.val then BitVec.ofNat 64 0 else value lane

def execVzeroUpper {Other : Type} (state : MachineState Other) : MachineState Other :=
  { state with zmm := fun register => vzeroUpperRegister register (state.zmm register) }

def execRet {Other : Type} (state : MachineState Other) : Except Fault (Outcome Other) :=
  let stack := state.gpr Gpr.rsp
  if readableBytes state.mem stack 8 then
    let returnAddress := loadQwordLE state.mem stack
    let nextStack := addressAdd stack 8
    .ok (.returned
      { state with
        gpr := setGpr state.gpr Gpr.rsp nextStack
        rip := returnAddress })
  else
    .error (.readFault stack)

theorem qword_bytes_length (word : QWord) :
    (qwordBytes word).length = 8 := by rfl

theorem storeByte_same (memory : Memory) (address : Addr) (value : Byte) :
    (storeByte memory address value).byte address = value := by
  simp [storeByte]

theorem storeByte_other (memory : Memory) (address other : Addr) (value : Byte)
    (hne : other ≠ address) :
    (storeByte memory address value).byte other = memory.byte other := by
  simp [storeByte, hne]

theorem storeByte_permissions (memory : Memory) (address : Addr) (value : Byte) :
    (storeByte memory address value).perm = memory.perm := by rfl

theorem storeBytes_permissions (memory : Memory) (base : Addr)
    (values : List Byte) :
    (storeBytes memory base values).perm = memory.perm := by
  induction values generalizing memory base with
  | nil => rfl
  | cons value rest ih =>
      simp only [storeBytes]
      rw [ih]
      rfl

theorem storeBytes_frame (memory : Memory) (base candidate : Addr)
    (values : List Byte) (hnot : candidate ∉ storeAddresses base values) :
    (storeBytes memory base values).byte candidate = memory.byte candidate := by
  induction values generalizing memory base with
  | nil => rfl
  | cons value rest ih =>
      simp only [storeAddresses, List.mem_cons, not_or] at hnot
      simp only [storeBytes]
      rw [ih (storeByte memory base value) (addressAdd base 1) hnot.2]
      exact storeByte_other memory base candidate value hnot.1

theorem storeQwordLE_permissions (memory : Memory) (base : Addr)
    (word : QWord) :
    (storeQwordLE memory base word).perm = memory.perm := by
  exact storeBytes_permissions memory base (qwordBytes word)

theorem storeQwordLE_frame (memory : Memory) (base candidate : Addr)
    (word : QWord) (hnot : candidate ∉ storeAddresses base (qwordBytes word)) :
    (storeQwordLE memory base word).byte candidate = memory.byte candidate := by
  exact storeBytes_frame memory base candidate (qwordBytes word) hnot

theorem qwordOfNat_mul (x y : Nat) :
    BitVec.ofNat 64 (x * y) = BitVec.ofNat 64 x * BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mul_mod]

/-- A little-endian qword store is read back exactly at the same address. -/
theorem loadQwordLE_storeQwordLE_same (memory : Memory) (base : Addr)
    (word : QWord) :
    loadQwordLE (storeQwordLE memory base word) base = word := by
  simp [loadQwordLE, storeQwordLE, storeBytes, storeByte, qwordBytes,
    qwordByte, addressAdd, Finset.sum_range_succ]
  simp only [BitVec.ofNat_add, qwordOfNat_mul, BitVec.ofNat_toNat]
  bv_decide

theorem storeZmm_permissions (memory : Memory) (base : Addr) (value : Zmm) :
    (storeZmm memory base value).perm = memory.perm := by
  simp only [storeZmm]
  repeat' rw [storeQwordLE_permissions]

theorem readableBytes_storeZmm (memory : Memory) (writeBase readBase : Addr)
    (value : Zmm) (count : Nat) :
    readableBytes (storeZmm memory writeBase value) readBase count =
      readableBytes memory readBase count := by
  simp only [readableBytes, storeZmm_permissions]

theorem writableBytes_storeZmm (memory : Memory) (writeBase testBase : Addr)
    (value : Zmm) (count : Nat) :
    writableBytes (storeZmm memory writeBase value) testBase count =
      writableBytes memory testBase count := by
  simp only [writableBytes, storeZmm_permissions]

theorem storeZmm_frame (memory : Memory) (base candidate : Addr) (value : Zmm)
    (hnot : candidate ∉ zmmWrittenAddresses base value) :
    (storeZmm memory base value).byte candidate = memory.byte candidate := by
  simp only [zmmWrittenAddresses, List.mem_append, not_or] at hnot
  rcases hnot with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  simp only [storeZmm]
  rw [storeQwordLE_frame _ _ _ _ h7]
  rw [storeQwordLE_frame _ _ _ _ h6]
  rw [storeQwordLE_frame _ _ _ _ h5]
  rw [storeQwordLE_frame _ _ _ _ h4]
  rw [storeQwordLE_frame _ _ _ _ h3]
  rw [storeQwordLE_frame _ _ _ _ h2]
  rw [storeQwordLE_frame _ _ _ _ h1]
  rw [storeQwordLE_frame _ _ _ _ h0]

theorem addressAdd_injective_below (base : Addr) {left right : Nat}
    (hleft : left < 2 ^ 64) (hright : right < 2 ^ 64)
    (hequal : addressAdd base left = addressAdd base right) : left = right := by
  have hequal' : BitVec.ofNat 64 left = BitVec.ofNat 64 right := by
    simpa [addressAdd] using congrArg (fun value => value - base) hequal
  have hnat := congrArg BitVec.toNat hequal'
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hnat
  exact hnat

def qwordRangesDisjoint (left right : Addr) : Prop :=
  ∀ leftOffset rightOffset,
    leftOffset < 8 → rightOffset < 8 →
      addressAdd left leftOffset ≠ addressAdd right rightOffset

theorem qwordRangesDisjoint_at_offsets (base : Addr) (left right : Nat)
    (hleft : left + 8 ≤ right ∨ right + 8 ≤ left)
    (hbound : left + 8 < 2 ^ 64 ∧ right + 8 < 2 ^ 64) :
    qwordRangesDisjoint (addressAdd base left) (addressAdd base right) := by
  intro leftOffset rightOffset hleftOffset hrightOffset hequal
  have hequal' : addressAdd base (left + leftOffset) =
      addressAdd base (right + rightOffset) := by
    simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using hequal
  have hoffset := addressAdd_injective_below base
    (left := left + leftOffset) (right := right + rightOffset)
    (by omega) (by omega) hequal'
  omega

theorem loadQwordLE_storeQwordLE_disjoint (memory : Memory)
    (readBase writeBase : Addr) (word : QWord)
    (hdisjoint : qwordRangesDisjoint readBase writeBase) :
    loadQwordLE (storeQwordLE memory writeBase word) readBase =
      loadQwordLE memory readBase := by
  unfold loadQwordLE
  congr 1
  apply Finset.sum_congr rfl
  intro offset hoffset
  rw [storeQwordLE_frame]
  simp only [qwordBytes, storeAddresses, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, not_or]
  constructor
  · simpa [addressAdd] using
      hdisjoint offset 0 (Finset.mem_range.mp hoffset) (by omega)
  constructor
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 1 (Finset.mem_range.mp hoffset) (by omega)
  constructor
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 2 (Finset.mem_range.mp hoffset) (by omega)
  constructor
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 3 (Finset.mem_range.mp hoffset) (by omega)
  constructor
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 4 (Finset.mem_range.mp hoffset) (by omega)
  constructor
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 5 (Finset.mem_range.mp hoffset) (by omega)
  constructor
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 6 (Finset.mem_range.mp hoffset) (by omega)
  · simpa [addressAdd, BitVec.ofNat_add, BitVec.add_assoc] using
      hdisjoint offset 7 (Finset.mem_range.mp hoffset) (by omega)

theorem loadQwordLE_storeQwordLE_offset_disjoint (memory : Memory)
    (base : Addr) (readOffset writeOffset : Nat) (word : QWord)
    (hdisjoint : readOffset + 8 ≤ writeOffset ∨
      writeOffset + 8 ≤ readOffset)
    (hbound : readOffset + 8 < 2 ^ 64 ∧ writeOffset + 8 < 2 ^ 64) :
    loadQwordLE
        (storeQwordLE memory (addressAdd base writeOffset) word)
        (addressAdd base readOffset) =
      loadQwordLE memory (addressAdd base readOffset) := by
  exact loadQwordLE_storeQwordLE_disjoint memory _ _ word
    (qwordRangesDisjoint_at_offsets base readOffset writeOffset hdisjoint hbound)

/-- Storing a complete ZMM and loading it at the same base is exact. -/
theorem loadZmm_storeZmm_same (memory : Memory) (base : Addr) (value : Zmm) :
    loadZmm (storeZmm memory base value) base = value := by
  funext lane
  fin_cases lane <;>
    simp only [loadZmm, storeZmm] <;>
    repeat' first
      | rw [loadQwordLE_storeQwordLE_same]
      | rw [loadQwordLE_storeQwordLE_offset_disjoint] <;> norm_num
  all_goals apply congrArg value; apply Fin.ext; rfl

/--
A complete ZMM store cannot change a disjoint 64-byte ZMM row. The explicit
offset and no-wrap premises make the byte-addressed frame condition visible to
callers rather than hiding it behind a mathematical array abstraction.
-/
theorem loadZmm_storeZmm_offset_disjoint (memory : Memory) (base : Addr)
    (readOffset writeOffset : Nat) (value : Zmm)
    (hdisjoint : readOffset + 64 ≤ writeOffset ∨
      writeOffset + 64 ≤ readOffset)
    (hbound : readOffset + 64 < 2 ^ 64 ∧ writeOffset + 64 < 2 ^ 64) :
    loadZmm
        (storeZmm memory (addressAdd base writeOffset) value)
        (addressAdd base readOffset) =
      loadZmm memory (addressAdd base readOffset) := by
  have preserve (original : Memory) (readDelta writeDelta : Nat)
      (word : QWord) (hreadDelta : readDelta + 8 ≤ 64)
      (hwriteDelta : writeDelta + 8 ≤ 64) :
      loadQwordLE
          (storeQwordLE original (addressAdd base (writeOffset + writeDelta)) word)
          (addressAdd base (readOffset + readDelta)) =
        loadQwordLE original (addressAdd base (readOffset + readDelta)) := by
    apply loadQwordLE_storeQwordLE_offset_disjoint
    · omega
    · omega
  funext lane
  simp only [loadZmm, storeZmm, addressAdd_nested]
  rw [preserve _ (8 * lane.val) 56 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 48 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 40 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 32 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 24 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 16 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 8 _ (by omega) (by omega)]
  rw [preserve _ (8 * lane.val) 0 _ (by omega) (by omega)]

/-- Byte-level disjointness between one eight-byte qword and one ZMM row. -/
def qwordZmmRangesDisjoint (qwordBase zmmBase : Addr) : Prop :=
  ∀ qwordOffset zmmOffset,
    qwordOffset < 8 → zmmOffset < 64 →
      addressAdd qwordBase qwordOffset ≠ addressAdd zmmBase zmmOffset

/-- A disjoint 64-byte vector store preserves an eight-byte return word. -/
theorem loadQwordLE_storeZmm_disjoint (memory : Memory)
    (qwordBase zmmBase : Addr) (value : Zmm)
    (hdisjoint : qwordZmmRangesDisjoint qwordBase zmmBase) :
    loadQwordLE (storeZmm memory zmmBase value) qwordBase =
      loadQwordLE memory qwordBase := by
  have hqword (delta : Nat) (hdelta : delta + 8 ≤ 64) :
      qwordRangesDisjoint qwordBase (addressAdd zmmBase delta) := by
    intro qwordOffset zmmOffset hqwordOffset hzmmOffset
    simpa [addressAdd_nested, Nat.add_comm delta zmmOffset] using
      hdisjoint qwordOffset (delta + zmmOffset) hqwordOffset (by omega)
  simp only [storeZmm]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 56 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 48 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 40 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 32 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 24 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 16 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 8 (by omega))]
  rw [loadQwordLE_storeQwordLE_disjoint _ _ _ _ (hqword 0 (by omega))]

theorem loadZmm_lane (memory : Memory) (base : Addr) (lane : Fin 8) :
    loadZmm memory base lane =
      loadQwordLE memory (addressAdd base (8 * lane.val)) := by
  rfl

theorem vmovdqu64Load_target {Other : Type} (state : MachineState Other) (target : ZReg)
    (base : Addr) :
    (vmovdqu64Load state target base).zmm target = loadZmm state.mem base := by
  simp [vmovdqu64Load, setZmm]

theorem vmovdqu64Load_other {Other : Type} (state : MachineState Other) (target other : ZReg)
    (base : Addr) (hne : other ≠ target) :
    (vmovdqu64Load state target base).zmm other = state.zmm other := by
  simp [vmovdqu64Load, setZmm, hne]

theorem vmovdqu64Load_memory {Other : Type} (state : MachineState Other) (target : ZReg)
    (base : Addr) :
    (vmovdqu64Load state target base).mem = state.mem := by rfl

theorem vmovdqu64Store_registers {Other : Type} (state : MachineState Other)
    (base : Addr) (source : ZReg) :
    (vmovdqu64Store state base source).gpr = state.gpr ∧
      (vmovdqu64Store state base source).zmm = state.zmm ∧
      (vmovdqu64Store state base source).opmask = state.opmask := by
  exact ⟨rfl, rfl, rfl⟩

theorem vmovdqu64Store_permissions {Other : Type} (state : MachineState Other)
    (base : Addr) (source : ZReg) :
    (vmovdqu64Store state base source).mem.perm = state.mem.perm := by
  exact storeZmm_permissions state.mem base (state.zmm source)

theorem execVmovdqu64Load_readable {Other : Type} (state : MachineState Other)
    (target : ZReg) (base : Addr)
    (hread : readableBytes state.mem base 64 = true) :
    execVmovdqu64Load state target base =
      .ok (vmovdqu64Load state target base) := by
  simp [execVmovdqu64Load, hread]

theorem execVmovdqu64Load_unreadable {Other : Type} (state : MachineState Other)
    (target : ZReg) (base : Addr)
    (hread : readableBytes state.mem base 64 = false) :
    execVmovdqu64Load state target base = .error (.readFault base) := by
  simp [execVmovdqu64Load, hread]

theorem execVmovdqu64Store_writable {Other : Type} (state : MachineState Other)
    (base : Addr) (source : ZReg)
    (hwrite : writableBytes state.mem base 64 = true) :
    execVmovdqu64Store state base source =
      .ok (vmovdqu64Store state base source) := by
  simp [execVmovdqu64Store, hwrite]

theorem execVmovdqu64Store_unwritable {Other : Type} (state : MachineState Other)
    (base : Addr) (source : ZReg)
    (hwrite : writableBytes state.mem base 64 = false) :
    execVmovdqu64Store state base source = .error (.writeFault base) := by
  simp [execVmovdqu64Store, hwrite]

theorem vzeroUpper_low128_preserved {Other : Type} (state : MachineState Other)
    (register : ZReg) (lane : Fin 8) (hlane : lane.val < 2) :
    (execVzeroUpper state).zmm register lane = state.zmm register lane := by
  simp [execVzeroUpper, vzeroUpperRegister]
  omega

theorem vzeroUpper_high_register_preserved {Other : Type} (state : MachineState Other)
    (register : ZReg) (hregister : 16 ≤ register.val) :
    (execVzeroUpper state).zmm register = state.zmm register := by
  funext lane
  simp [execVzeroUpper, vzeroUpperRegister]
  omega

theorem vzeroUpper_low_register_upper_cleared {Other : Type} (state : MachineState Other)
    (register : ZReg) (lane : Fin 8) (hregister : register.val < 16)
    (hlane : 2 ≤ lane.val) :
    (execVzeroUpper state).zmm register lane = BitVec.ofNat 64 0 := by
  simp [execVzeroUpper, vzeroUpperRegister, hregister, hlane]

theorem vzeroUpper_memory_preserved {Other : Type} (state : MachineState Other) :
    (execVzeroUpper state).mem = state.mem := by rfl

theorem execRet_readable {Other : Type} (state : MachineState Other)
    (hread : readableBytes state.mem (state.gpr Gpr.rsp) 8 = true) :
    execRet state = .ok (.returned
      { state with
        gpr := setGpr state.gpr Gpr.rsp
          (addressAdd (state.gpr Gpr.rsp) 8)
        rip := loadQwordLE state.mem (state.gpr Gpr.rsp) }) := by
  simp [execRet, hread]

theorem execRet_unreadable {Other : Type} (state : MachineState Other)
    (hread : readableBytes state.mem (state.gpr Gpr.rsp) 8 = false) :
    execRet state = .error (.readFault (state.gpr Gpr.rsp)) := by
  simp [execRet, hread]

end NaryaFormal.X86
