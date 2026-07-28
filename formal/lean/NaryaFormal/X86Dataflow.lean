/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Definite-assignment analysis for the exact decoded r51 multiplier schedule.
This is deliberately separate from the arithmetic proof: it establishes that
every ZMM value consumed by the straight-line body was either supplied by an
input load, produced by an input-independent clear/broadcast, or written by an
earlier arithmetic instruction. It is the static premise needed to remove any
fiction that caller-owned scratch registers begin at zero.
-/

import NaryaFormal.GeneratedR51InstructionTrace

namespace NaryaFormal.X86

abbrev DefinedRegisters := ZReg → Bool

def noRegistersDefined : DefinedRegisters := fun _ => false

def registersBelow (limit : Nat) : DefinedRegisters :=
  fun register => decide (register.val < limit)

def defineRegister (defined : DefinedRegisters) (target : ZReg) :
    DefinedRegisters :=
  fun register => if register = target then true else defined register

/--
ZMM inputs on which an instruction's relevant result depends. `x xor x` has
no dependency because every output bit is zero independently of the old
register contents. Loads and broadcasts likewise define their destinations
from memory rather than from a prior ZMM value.
-/
def instructionDependencies : Instruction → List ZReg
  | .vmovdqu64Load .. => []
  | .vmovdqu64Store _ _ source => [source]
  | .vpxorq _ source1 source2 =>
      if source1 = source2 then [] else [source1, source2]
  | .vpmadd52luq destination source1 source2
  | .vpmadd52huq destination source1 source2 =>
      [destination, source1, source2]
  | .vpaddq _ source1 source2
  | .vpmullq _ source1 source2
  | .vpandq _ source1 source2 => [source1, source2]
  | .vpsllq _ source _
  | .vpsrlq _ source _ => [source]
  | .vpbroadcastq .. => []
  | .vzeroUpper => []
  | .ret => []

def instructionWrites : Instruction → List ZReg
  | .vmovdqu64Load destination ..
  | .vpxorq destination ..
  | .vpmadd52luq destination ..
  | .vpmadd52huq destination ..
  | .vpaddq destination ..
  | .vpmullq destination ..
  | .vpandq destination ..
  | .vpsllq destination ..
  | .vpsrlq destination ..
  | .vpbroadcastq destination .. => [destination]
  | .vmovdqu64Store .. | .vzeroUpper | .ret => []

def dependenciesDefined (defined : DefinedRegisters)
    (instruction : Instruction) : Bool :=
  (instructionDependencies instruction).all defined

def addInstructionWrites (defined : DefinedRegisters)
    (instruction : Instruction) : DefinedRegisters :=
  (instructionWrites instruction).foldl defineRegister defined

def propagateDefined :
    List Instruction → DefinedRegisters → Option DefinedRegisters
  | [], defined => some defined
  | instruction :: rest, defined =>
      if dependenciesDefined defined instruction then
        propagateDefined rest (addInstructionWrites defined instruction)
      else
        none

def registersAreDefined (defined : DefinedRegisters)
    (registers : List ZReg) : Bool :=
  registers.all defined

def decodedBody : List Instruction :=
  GeneratedR51InstructionTrace.loadPhase ++
    GeneratedR51InstructionTrace.clearPhase ++
      GeneratedR51InstructionTrace.arithmeticCorePhase ++
        GeneratedR51InstructionTrace.storePhase

def outputRegisters : List ZReg :=
  [⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩,
    ⟨13, by decide⟩, ⟨14, by decide⟩]

def bodyLeavesOutputsDefined : Bool :=
  match propagateDefined decodedBody noRegistersDefined with
  | some defined => registersAreDefined defined outputRegisters
  | none => false

/--
Starting with no caller ZMM register assumed initialized, the exact decoded
load/clear/arithmetic/store body never consumes an undefined ZMM value and
leaves every output register defined.
-/
theorem decoded_body_definite_assignment : bodyLeavesOutputsDefined = true := by
  native_decide

def arithmeticCoreScratchDefined : Bool :=
    match propagateDefined GeneratedR51InstructionTrace.arithmeticCorePhase
        (registersBelow 28) with
    | some defined =>
        registersAreDefined defined [⟨28, by decide⟩, ⟨30, by decide⟩] &&
          !defined ⟨29, by decide⟩ && !defined ⟨31, by decide⟩
    | none => false

/--
In particular, ZMM28 and ZMM30 are written before their first arithmetic use;
ZMM29 and ZMM31 are never dependencies. This certificate is what permits the
future entry theorem to ignore their arbitrary caller-owned entry values.
-/
theorem arithmetic_core_definite_assignment :
    arithmeticCoreScratchDefined = true := by
  native_decide

/--
The exact arithmetic core is dependency-safe from the ABI-realistic initial
set ZMM0--27 and leaves all five output registers semantically defined.
-/
theorem arithmetic_core_defined_outputs :
    ∃ after,
      propagateDefined GeneratedR51InstructionTrace.arithmeticCorePhase
          (registersBelow 28) = some after ∧
      after ⟨10, by decide⟩ = true ∧ after ⟨11, by decide⟩ = true ∧
      after ⟨12, by decide⟩ = true ∧ after ⟨13, by decide⟩ = true ∧
      after ⟨14, by decide⟩ = true := by
  native_decide

end NaryaFormal.X86
