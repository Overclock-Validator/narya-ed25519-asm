/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Kernel-checked correspondence between the exact canonical linked bytes and the
expanded instruction trace extracted independently from assembly source. This
closes the byte-to-instruction-list link for narya_r51x8_mul_ifma; execution
refinement and the complete System V postcondition remain separate theorems.
-/

import NaryaFormal.GeneratedR51InstructionTrace

namespace NaryaFormal.X86

open GeneratedR51InstructionTrace

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem r51_object_decodes_to_source_instruction_trace :
    decodeProgram R51Object.symbolAddress R51Object.symbolBytes =
      some expectedProgram := by
  decide

theorem r51_object_instruction_count : expectedProgram.length = 129 :=
  expected_instruction_count

def Instruction.isVectorLoad : Instruction → Bool
  | .vmovdqu64Load .. => true
  | _ => false

def Instruction.isVectorStore : Instruction → Bool
  | .vmovdqu64Store .. => true
  | _ => false

set_option maxRecDepth 4096 in
theorem r51_first_ten_instructions_are_source_loads :
    (expectedProgram.take 10).all Instruction.isVectorLoad = true := by
  decide

set_option maxRecDepth 4096 in
theorem r51_no_output_store_before_all_arithmetic_finishes :
    (expectedProgram.take 122).all
      (fun instruction => !instruction.isVectorStore) = true := by
  decide

set_option maxRecDepth 4096 in
theorem r51_exact_output_store_suffix :
    (expectedProgram.drop 122).take 5 = [
      .vmovdqu64Store .rdi 0 ⟨10, by decide⟩,
      .vmovdqu64Store .rdi 64 ⟨11, by decide⟩,
      .vmovdqu64Store .rdi 128 ⟨12, by decide⟩,
      .vmovdqu64Store .rdi 192 ⟨13, by decide⟩,
      .vmovdqu64Store .rdi 256 ⟨14, by decide⟩] := by
  decide

set_option maxRecDepth 4096 in
theorem r51_epilogue_is_vzeroupper_ret :
    expectedProgram.drop 127 = [.vzeroUpper, .ret] := by
  decide

end NaryaFormal.X86
