/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Exact refinement of the decoded `VZEROUPPER; RET` suffix. This theorem begins
after the output stores. Composing it with the body requires a separate premise
that those stores do not overwrite the eight-byte return-address slot.
-/

import NaryaFormal.X86BodyRefinement

namespace NaryaFormal.X86

def returnedR51State {Other : Type} (state : MachineState Other) :
    MachineState Other :=
  { execVzeroUpper state with
    gpr := setGpr state.gpr .rsp (addressAdd (state.gpr .rsp) 8)
    rip := loadQwordLE state.mem (state.gpr .rsp) }

/--
The exact decoded epilogue has the architectural `VZEROUPPER` effect, pops one
readable return address, advances RSP by eight, and changes no memory.
-/
theorem run_epilogue_refines {Other : Type} (state : MachineState Other)
    (hreturn : readableBytes state.mem (state.gpr .rsp) 8 = true) :
    runProgram GeneratedR51InstructionTrace.epiloguePhase state =
      .ok (.returned (returnedR51State state)) := by
  have hreturnZeroed : readableBytes (execVzeroUpper state).mem
      ((execVzeroUpper state).gpr .rsp) 8 = true := by
    simpa [execVzeroUpper] using hreturn
  rw [GeneratedR51InstructionTrace.epiloguePhase]
  simp only [runProgram, executeInstruction]
  rw [execRet_readable (execVzeroUpper state) hreturnZeroed]
  rfl

/-- Compose any successfully proved decoded body with the exact epilogue. -/
theorem run_expected_program_after_body {Other : Type}
    (state bodyNext : MachineState Other)
    (hbody : runMachinePhase decodedBody state = .ok bodyNext)
    (hreturn : readableBytes bodyNext.mem (bodyNext.gpr .rsp) 8 = true) :
    runProgram GeneratedR51InstructionTrace.expectedProgram state =
      .ok (.returned (returnedR51State bodyNext)) := by
  have hsplit : GeneratedR51InstructionTrace.expectedProgram =
      decodedBody ++ GeneratedR51InstructionTrace.epiloguePhase := by
    simp [GeneratedR51InstructionTrace.expectedProgram, decodedBody,
      GeneratedR51InstructionTrace.arithmeticCorePhase]
  rw [hsplit, runProgram_append_of_runMachinePhase _ _ _ _ hbody]
  exact run_epilogue_refines bodyNext hreturn

theorem returned_r51_memory_preserved {Other : Type} (state : MachineState Other) :
    (returnedR51State state).mem = state.mem := by
  rfl

theorem returned_r51_stack_advanced {Other : Type} (state : MachineState Other) :
    (returnedR51State state).gpr .rsp = addressAdd (state.gpr .rsp) 8 := by
  simp [returnedR51State, setGpr]

theorem returned_r51_rip {Other : Type} (state : MachineState Other) :
    (returnedR51State state).rip = loadQwordLE state.mem (state.gpr .rsp) := by
  rfl

theorem returned_r51_other_gpr {Other : Type} (state : MachineState Other)
    (register : Gpr) (hregister : register ≠ .rsp) :
    (returnedR51State state).gpr register = state.gpr register := by
  simp [returnedR51State, setGpr, hregister]

theorem returned_r51_zmm_effect {Other : Type} (state : MachineState Other) :
    (returnedR51State state).zmm = (execVzeroUpper state).zmm := by
  rfl

end NaryaFormal.X86
