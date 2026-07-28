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

end NaryaFormal.X86
