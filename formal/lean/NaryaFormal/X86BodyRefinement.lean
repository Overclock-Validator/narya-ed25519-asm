/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Composition of the decoded r51 multiplier body: ten source loads, eighteen
clears, the 94-instruction arithmetic core, and five output stores. Because
every source load completes before the first store, the theorem requires no
source/output disjointness and therefore covers exact and partial aliasing.
The VZEROUPPER/RET epilogue remains a separate ABI theorem.
-/

import NaryaFormal.X86InputRefinement
import NaryaFormal.X86MemoryRefinement

namespace NaryaFormal.X86

/--
The complete non-returning decoded body writes the mathematical five-limb
product for one selected lane, preserves permissions/GPRs, and changes no byte
outside the exact five output rows.
-/
theorem run_decoded_body_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (state : MachineState Other)
    (hx : Radix51.AssemblyTrace.LimbsU52 environment.x)
    (hy : Radix51.AssemblyTrace.LimbsU52 environment.y)
    (hinput : R51InputMemory environment lane state)
    (hconstants : R51ConstantMemory state)
    (hwrite : ∀ limb : Fin 5,
      writableBytes state.mem (outputRowAddress state limb) 64 = true) :
    ∃ arithmetic next : MachineState Other,
      runMachinePhase decodedBody state = .ok next ∧
      next = storedR51OutputState arithmetic ∧
      arithmetic.mem = state.mem ∧
      arithmetic.gpr = state.gpr ∧
      (∀ limb : Fin 5,
        (loadZmm next.mem (outputRowAddress state limb) lane).toNat =
          (storedNatShadowState environment).output limb) ∧
      next.mem.perm = state.mem.perm ∧
      next.gpr = state.gpr ∧
      (∀ candidate, candidate ∉ outputWrittenAddresses arithmetic →
        next.mem.byte candidate = state.mem.byte candidate) := by
  rcases run_prepare_phase environment lane state hinput with
    ⟨prepared, hprepare, hagrees, hprepareMem, hprepareGpr⟩
  have hpreparedConstants : R51ConstantMemory prepared := by
    constructor
    · simpa [hprepareMem] using hconstants.foldReadable
    · simpa [hprepareMem] using hconstants.foldValue
    · simpa [hprepareMem] using hconstants.maskReadable
    · simpa [hprepareMem] using hconstants.maskValue
  rcases run_arithmetic_core_ignores_undefined_scratch environment lane
      prepared hx hy hpreparedConstants hagrees with
    ⟨arithmetic, harithmetic, h10, h11, h12, h13, h14, harithmeticMem⟩
  have harithmeticGpr : arithmetic.gpr = prepared.gpr :=
    runCorePhase_gpr_preserved
      GeneratedR51InstructionTrace.arithmeticCorePhase prepared arithmetic
      arithmetic_core_instructions_admitted harithmetic
  have hwriteArithmetic : ∀ limb : Fin 5,
      writableBytes arithmetic.mem (outputRowAddress arithmetic limb) 64 = true := by
    intro limb
    simpa [outputRowAddress, harithmeticMem, hprepareMem, harithmeticGpr,
      hprepareGpr] using hwrite limb
  have hstore := run_store_phase arithmetic hwriteArithmetic
  let next := storedR51OutputState arithmetic
  have houtput (limb : Fin 5) :
      (arithmetic.zmm (outputRegister limb) lane).toNat =
        (normalizedNatShadowState environment).zmm (outputRegister limb) := by
    fin_cases limb
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
  have hrows : ∀ limb : Fin 5,
      (loadZmm next.mem (outputRowAddress state limb) lane).toNat =
        (storedNatShadowState environment).output limb := by
    intro limb
    have haddress : outputRowAddress arithmetic limb =
        outputRowAddress state limb := by
      simp [outputRowAddress, harithmeticGpr, hprepareGpr]
    rw [← haddress]
    change (loadZmm (storedR51OutputState arithmetic).mem
      (outputRowAddress arithmetic limb) lane).toNat = _
    rw [stored_output_rows_exact arithmetic limb]
    rw [houtput limb]
    exact normalized_output_register environment limb
  refine ⟨arithmetic, next, ?_, rfl, harithmeticMem.trans hprepareMem,
    harithmeticGpr.trans hprepareGpr, hrows, ?_, ?_, ?_⟩
  · have hsplit : decodedBody =
        (GeneratedR51InstructionTrace.loadPhase ++
          GeneratedR51InstructionTrace.clearPhase) ++
        (GeneratedR51InstructionTrace.arithmeticCorePhase ++
          GeneratedR51InstructionTrace.storePhase) := by
      simp [decodedBody]
    rw [hsplit, runMachinePhase_append, hprepare]
    change runMachinePhase
      (GeneratedR51InstructionTrace.arithmeticCorePhase ++
        GeneratedR51InstructionTrace.storePhase) prepared = .ok next
    rw [runMachinePhase_append, harithmetic]
    exact hstore
  · exact (stored_output_permissions_preserved arithmetic).trans
      (by simp [harithmeticMem, hprepareMem])
  · exact (stored_output_registers_preserved arithmetic).1.trans
      (harithmeticGpr.trans hprepareGpr)
  · intro candidate hnot
    rw [stored_output_frame arithmetic candidate hnot]
    simp [harithmeticMem, hprepareMem]

end NaryaFormal.X86
