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

/--
End-to-end refinement of the decoded SysV multiplier leaf. The only forbidden
alias is the one imposed by `RET`: none of the five output rows may overwrite
the eight-byte return-address slot. Inputs may otherwise overlap outputs in any
way because all ten source rows are loaded before the first store.

The theorem deliberately exposes the exact returned machine state as well as
the selected-lane mathematical result. This makes the ABI boundary auditable:
the output frame is exact, permissions are unchanged, RSP advances by eight,
and RIP is the return address present on entry.
-/
theorem run_r51_multiplier_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (state : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hinput : R51InputMemory environment lane state)
    (hconstants : R51ConstantMemory state)
    (hwrite : ∀ limb : Fin 5,
      writableBytes state.mem (outputRowAddress state limb) 64 = true)
    (hreturn : readableBytes state.mem (state.gpr .rsp) 8 = true)
    (hstack : stackOutputRowsDisjoint state) :
    ∃ arithmetic bodyNext : MachineState Other,
      runProgram GeneratedR51InstructionTrace.expectedProgram state =
        .ok (.returned (returnedR51State bodyNext)) ∧
      bodyNext = storedR51OutputState arithmetic ∧
      (∀ limb : Fin 5,
        (loadZmm (returnedR51State bodyNext).mem
          (outputRowAddress state limb) lane).toNat =
            (storedNatShadowState environment).output limb) ∧
      (returnedR51State bodyNext).mem.perm = state.mem.perm ∧
      (returnedR51State bodyNext).gpr .rsp = addressAdd (state.gpr .rsp) 8 ∧
      (returnedR51State bodyNext).rip =
        loadQwordLE state.mem (state.gpr .rsp) ∧
      (∀ register, register ≠ .rsp →
        (returnedR51State bodyNext).gpr register = state.gpr register) ∧
      (∀ candidate, candidate ∉ outputWrittenAddresses arithmetic →
        (returnedR51State bodyNext).mem.byte candidate =
          state.mem.byte candidate) := by
  rcases run_decoded_body_refines environment lane state hx hy hinput
      hconstants hwrite with
    ⟨arithmetic, bodyNext, hbody, hbodyStore, harithmeticMem,
      harithmeticGpr, hrows, hbodyPerm, hbodyGpr, hframe⟩
  have hstackArithmetic : stackOutputRowsDisjoint arithmetic := by
    intro limb
    simpa [outputRowAddress, harithmeticGpr] using hstack limb
  have hreturnWord :
      loadQwordLE bodyNext.mem (bodyNext.gpr .rsp) =
        loadQwordLE state.mem (state.gpr .rsp) := by
    rw [hbodyStore]
    calc
      loadQwordLE (storedR51OutputState arithmetic).mem
          ((storedR51OutputState arithmetic).gpr .rsp) =
          loadQwordLE arithmetic.mem (arithmetic.gpr .rsp) := by
            rw [(stored_output_registers_preserved arithmetic).1]
            exact stored_output_return_word arithmetic hstackArithmetic
      _ = loadQwordLE state.mem (state.gpr .rsp) := by
        rw [harithmeticMem, harithmeticGpr]
  have hreturnBody :
      readableBytes bodyNext.mem (bodyNext.gpr .rsp) 8 = true := by
    unfold readableBytes at hreturn ⊢
    simpa [hbodyPerm, hbodyGpr] using hreturn
  have hprogram := run_expected_program_after_body state bodyNext hbody hreturnBody
  refine ⟨arithmetic, bodyNext, hprogram, hbodyStore, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro limb
    simpa [returnedR51State, execVzeroUpper] using hrows limb
  · simpa [returnedR51State, execVzeroUpper] using hbodyPerm
  · rw [returned_r51_stack_advanced, hbodyGpr]
  · rw [returned_r51_rip, hreturnWord]
  · intro register hregister
    rw [returned_r51_other_gpr bodyNext register hregister, hbodyGpr]
  · intro candidate hnot
    simpa [returnedR51State, execVzeroUpper] using hframe candidate hnot

end NaryaFormal.X86
