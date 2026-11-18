/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Shared scaffolding for leaf theorems about Go-linked ABI0 symbols.

A Go assembly field leaf is a short prelude of stack-argument loads followed
by a vector program. Everything that does not depend on which leaf it is lives
here: the symbol decoder for a given argument count, the two prelude shapes in
use, the composition of a checker-accepted body with the prelude and the
return sequence, the read-back of the five output rows, and a satisfiability
witness built from a leaf specification.

A leaf file then supplies its bytes, its `LeafSpec`, kernel evaluations of the
decoder and the checker, and one arithmetic lemma.
-/

import NaryaFormal.X86GoR51MulReflective

namespace NaryaFormal.IfmaSym.GoLeaf

open NaryaFormal.X86
open NaryaFormal.Radix51
open NaryaFormal.IfmaSym.GoR51Mul (StackLoad decodeStackLoad execStackLoad
  runPrelude runGoSymbol)
open NaryaFormal.IfmaSym.R51Mul (outputLimbs leafPost_output_at)

/-! ### Decoder -/

/-- Decode a whole Go symbol: `argumentCount` five-byte stack-argument loads
followed by a vector program that must end in `RET` at the last symbol byte. -/
def decodeGoSymbol (argumentCount symbolAddress : Nat) (bytes : List Nat) :
    Option (List StackLoad × List Instruction) := do
  let prelude ← (List.range argumentCount).mapM
    (fun index => decodeStackLoad bytes (5 * index))
  let program ← decodeProgram (symbolAddress + 5 * argumentCount)
    (bytes.drop (5 * argumentCount))
  some (prelude, program)


variable {Other : Type}

/-! ### Argument preludes -/

/-- `func(out, x)`: `out` at `8(SP)` into RDI, `x` at `16(SP)` into RCX. -/
def prelude2 : List StackLoad := [⟨.rdi, 8⟩, ⟨.rcx, 16⟩]

/-- `func(out, x, y)`: as `prelude2`, then `y` at `24(SP)` into RBX. -/
def prelude3 : List StackLoad := [⟨.rdi, 8⟩, ⟨.rcx, 16⟩, ⟨.rbx, 24⟩]

/-- The pointer argument in the stack slot at `displacement(SP)`. -/
def argument (entry : MachineState Other) (displacement : Nat) : Addr :=
  loadQwordLE entry.mem (addressAdd (entry.gpr .rsp) displacement)

/-- Machine state after `prelude2`. -/
def bodyEntry2 (entry : MachineState Other) : MachineState Other :=
  { entry with
    gpr := setGpr (setGpr entry.gpr .rdi (argument entry 8)) .rcx
      (argument entry 16) }

/-- Machine state after `prelude3`. -/
def bodyEntry3 (entry : MachineState Other) : MachineState Other :=
  { entry with
    gpr := setGpr (setGpr (setGpr entry.gpr .rdi (argument entry 8)) .rcx
      (argument entry 16)) .rbx (argument entry 24) }


theorem bodyEntry2_frame (entry : MachineState Other) :
    (bodyEntry2 entry).mem = entry.mem ∧
    (bodyEntry2 entry).gpr .rsp = entry.gpr .rsp ∧
    (bodyEntry2 entry).gpr .rdi = argument entry 8 ∧
    (bodyEntry2 entry).gpr .rcx = argument entry 16 := by
  simp [bodyEntry2, setGpr]


theorem bodyEntry3_frame (entry : MachineState Other) :
    (bodyEntry3 entry).mem = entry.mem ∧
    (bodyEntry3 entry).gpr .rsp = entry.gpr .rsp ∧
    (bodyEntry3 entry).gpr .rdi = argument entry 8 ∧
    (bodyEntry3 entry).gpr .rcx = argument entry 16 ∧
    (bodyEntry3 entry).gpr .rbx = argument entry 24 := by
  simp [bodyEntry3, setGpr]


theorem run_prelude2 (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 16 = true) :
    runPrelude prelude2 entry = .ok (bodyEntry2 entry) := by
  have h8 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 16 0 8 harguments (by omega)
  have h16 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 16) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 16 8 8 harguments (by omega)
  simp [prelude2, runPrelude, execStackLoad, setGpr, h8, h16, bodyEntry2,
    argument]


theorem run_prelude3 (entry : MachineState Other)
    (harguments :
      readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 24 = true) :
    runPrelude prelude3 entry = .ok (bodyEntry3 entry) := by
  have h8 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 8) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 24 0 8 harguments (by omega)
  have h16 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 16) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 24 8 8 harguments (by omega)
  have h24 : readableBytes entry.mem (addressAdd (entry.gpr .rsp) 24) 8 = true := by
    simpa [addressAdd_nested] using
      readableBytes_sub _ _ 24 16 8 harguments (by omega)
  simp [prelude3, runPrelude, execStackLoad, setGpr, h8, h16, h24, bodyEntry3,
    argument]


/-! ### Composition -/

/-- If the prelude runs to `body` without touching memory or RSP, and the
checker accepts `vectorBody` under a contract that holds at `body`, then the
whole symbol returns normally and `LeafPost` holds relative to `body`. -/
theorem go_leaf_run (leafSpec : LeafSpec) (prelude : List StackLoad)
    (vectorBody : List Instruction) (final : SymState)
    (haccepts : runSym leafSpec vectorBody initialSymState = some final)
    (lane : Fin 8) (entry body : MachineState Other)
    (hprelude : runPrelude prelude entry = .ok body)
    (hmem : body.mem = entry.mem) (hrsp : body.gpr .rsp = entry.gpr .rsp)
    (hpre : LeafPre leafSpec lane body)
    (hreturn : readableBytes entry.mem (entry.gpr .rsp) 8 = true)
    (hstack : ∀ offset, offset < 8 →
      OutsideOutput leafSpec body (addressAdd (entry.gpr .rsp) offset)) :
    ∃ returned,
      runGoSymbol prelude (vectorBody ++ epilogue) entry =
        .ok (.returned returned) ∧
      LeafPost leafSpec lane final body returned := by
  have hreturnBody : readableBytes body.mem (body.gpr .rsp) 8 = true := by
    rw [hmem, hrsp]
    exact hreturn
  have hstackBody : ∀ offset, offset < 8 →
      OutsideOutput leafSpec body (addressAdd (body.gpr .rsp) offset) := by
    intro offset hoffset
    rw [hrsp]
    exact hstack offset hoffset
  obtain ⟨returned, hrun, hpost⟩ :=
    run_leaf leafSpec lane body hpre vectorBody final haccepts hreturnBody
      hstackBody
  refine ⟨returned, ?_, hpost⟩
  unfold runGoSymbol
  rw [hprelude]
  exact hrun


/-- The checker's five output expressions evaluated on entry memory. -/
def outputValues (final : SymState) (inputs : Gpr → Nat → Nat) : Loose5 :=
  ⟨(outputExpr final 0).eval inputs, (outputExpr final 64).eval inputs,
    (outputExpr final 128).eval inputs, (outputExpr final 192).eval inputs,
    (outputExpr final 256).eval inputs⟩


/-- Under `LeafPost`, the five machine output rows are the checker's output
expressions on entry memory, each within its tracked bound. -/
theorem output_rows (leafSpec : LeafSpec) (final : SymState)
    (hbase : leafSpec.outputBase = Gpr.rdi)
    (hdefined : outputDefined final 0 = true ∧ outputDefined final 64 = true ∧
      outputDefined final 128 = true ∧ outputDefined final 192 = true ∧
      outputDefined final 256 = true)
    (lane : Fin 8) (entry returned : MachineState Other)
    (hpost : LeafPost leafSpec lane final entry returned) :
    outputLimbs lane entry returned =
        outputValues final (entryInputs lane entry) ∧
      (outputLimbs lane entry returned).l0 ≤ outputBound final 0 ∧
      (outputLimbs lane entry returned).l1 ≤ outputBound final 64 ∧
      (outputLimbs lane entry returned).l2 ≤ outputBound final 128 ∧
      (outputLimbs lane entry returned).l3 ≤ outputBound final 192 ∧
      (outputLimbs lane entry returned).l4 ≤ outputBound final 256 := by
  obtain ⟨hd0, hd1, hd2, hd3, hd4⟩ := hdefined
  obtain ⟨hv0, hl0⟩ := leafPost_output_at hpost 0 hd0
  obtain ⟨hv1, hl1⟩ := leafPost_output_at hpost 64 hd1
  obtain ⟨hv2, hl2⟩ := leafPost_output_at hpost 128 hd2
  obtain ⟨hv3, hl3⟩ := leafPost_output_at hpost 192 hd3
  obtain ⟨hv4, hl4⟩ := leafPost_output_at hpost 256 hd4
  rw [hbase] at hv0 hv1 hv2 hv3 hv4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [outputLimbs, outputValues, Loose5.mk.injEq]
    exact ⟨hv0, hv1, hv2, hv3, hv4⟩
  · exact le_of_eq_of_le hv0 hl0
  · exact le_of_eq_of_le hv1 hl1
  · exact le_of_eq_of_le hv2 hl2
  · exact le_of_eq_of_le hv3 hl3
  · exact le_of_eq_of_le hv4 hl4


/-- The five 64-byte rows read through `base`, as a loose element. -/
def inputLoose (inputs : Gpr → Nat → Nat) (base : Gpr) : Loose5 :=
  ⟨inputs base 0, inputs base 64, inputs base 128, inputs base 192,
    inputs base 256⟩


/-- Rows of a u52 field element through `base`. -/
def u52Rows (base : Gpr) : List InputRow :=
  [⟨base, 0, 2 ^ 52 - 1⟩, ⟨base, 64, 2 ^ 52 - 1⟩, ⟨base, 128, 2 ^ 52 - 1⟩,
    ⟨base, 192, 2 ^ 52 - 1⟩, ⟨base, 256, 2 ^ 52 - 1⟩]


/-- The leaf contract bounds every selected-lane limb of a declared u52
element. -/
theorem input_u52 (leafSpec : LeafSpec) (lane : Fin 8)
    (entry : MachineState Other) (hpre : LeafPre leafSpec lane entry)
    (base : Gpr) (hrows : ∀ row ∈ u52Rows base, row ∈ leafSpec.inputs) :
    (inputLoose (entryInputs lane entry) base).l0 ≤ 2 ^ 52 - 1 ∧
    (inputLoose (entryInputs lane entry) base).l1 ≤ 2 ^ 52 - 1 ∧
    (inputLoose (entryInputs lane entry) base).l2 ≤ 2 ^ 52 - 1 ∧
    (inputLoose (entryInputs lane entry) base).l3 ≤ 2 ^ 52 - 1 ∧
    (inputLoose (entryInputs lane entry) base).l4 ≤ 2 ^ 52 - 1 :=
  ⟨hpre.inputBound ⟨base, 0, 2 ^ 52 - 1⟩ (hrows _ (by simp [u52Rows])),
    hpre.inputBound ⟨base, 64, 2 ^ 52 - 1⟩ (hrows _ (by simp [u52Rows])),
    hpre.inputBound ⟨base, 128, 2 ^ 52 - 1⟩ (hrows _ (by simp [u52Rows])),
    hpre.inputBound ⟨base, 192, 2 ^ 52 - 1⟩ (hrows _ (by simp [u52Rows])),
    hpre.inputBound ⟨base, 256, 2 ^ 52 - 1⟩ (hrows _ (by simp [u52Rows]))⟩


/-! ### Satisfiability witness -/

/-- Memory holding each declared constant at its address, zero elsewhere, with
every byte readable and writable. -/
def witnessMemory (constants : List Constant) : Memory :=
  { byte := fun address =>
      match constants.find? (fun constant =>
        decide (constant.address ≤ address.toNat ∧
          address.toNat < constant.address + 8)) with
      | some constant =>
          BitVec.ofNat 8
            (constant.value / 256 ^ (address.toNat - constant.address))
      | none => BitVec.ofNat 8 0
    perm := fun _ => ⟨true, true, false⟩ }


/-- Every register is zero except RSP, which is `2^21`. All pointer arguments
are therefore zero. -/
def witnessEntry (constants : List Constant) : MachineState Unit :=
  { gpr := fun register =>
      if register = .rsp then BitVec.ofNat 64 (2 ^ 21) else BitVec.ofNat 64 0
    zmm := fun _ _ => BitVec.ofNat 64 0
    opmask := fun _ => BitVec.ofNat 64 0
    rflags := BitVec.ofNat 64 0
    mxcsr := BitVec.ofNat 32 0
    mem := witnessMemory constants
    rip := BitVec.ofNat 64 0
    other := () }


/-- A leaf contract is satisfiable at the witness state once three facts are
checked by evaluation: the output pointer is zero after the prelude, the input
rows meet their bounds, and the constants read back their values. -/
theorem witness_contract (spec : LeafSpec) (argumentBytes : Nat)
    (body : MachineState Unit)
    (hmem : body.mem = witnessMemory spec.constants)
    (hbase : body.gpr spec.outputBase = BitVec.ofNat 64 0)
    (hbytes : spec.outputBytes ≤ 2 ^ 20)
    (hinputs : ∀ row ∈ spec.inputs,
      entryInputs 0 body row.base row.displacement ≤ row.bound)
    (hconstants : ∀ constant ∈ spec.constants,
      (constant.address < 2 ^ 64 ∧ constant.value < 2 ^ 64) ∧
      loadQwordLE body.mem (BitVec.ofNat 64 constant.address) =
        BitVec.ofNat 64 constant.value) :
    readableBytes (witnessEntry spec.constants).mem
        (addressAdd ((witnessEntry spec.constants).gpr .rsp) 8)
        argumentBytes = true ∧
      LeafPre spec 0 body ∧
      readableBytes (witnessEntry spec.constants).mem
        ((witnessEntry spec.constants).gpr .rsp) 8 = true ∧
      ∀ offset, offset < 8 →
        OutsideOutput spec body
          (addressAdd ((witnessEntry spec.constants).gpr .rsp) offset) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [readableBytes, witnessEntry, witnessMemory]
  · exact
      { outputBound := lt_of_le_of_lt hbytes (by norm_num)
        inputReadable := by
          intro row _
          simp [readableBytes, hmem, witnessMemory]
        inputBound := hinputs
        constantRange := fun constant hmember => (hconstants constant hmember).1
        constantReadable := by
          intro constant _
          simp [readableBytes, hmem, witnessMemory]
        constantValue := fun constant hmember => (hconstants constant hmember).2
        outputWritable := by
          simp [writableBytes, hmem, witnessMemory] }
  · simp [readableBytes, witnessEntry, witnessMemory]
  · intro offset hoffset inner hinner
    have hrsp : (witnessEntry spec.constants).gpr .rsp =
        BitVec.ofNat 64 (2 ^ 21) := rfl
    rw [hbase, hrsp]
    exact addressAdd_ofNat_ne (2 ^ 21) 0 offset inner (by omega) (by omega)
      (by omega)

end NaryaFormal.IfmaSym.GoLeaf
