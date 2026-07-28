/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Byte-memory refinement for the exact five-store suffix of the linked r51
multiplier. This module intentionally starts after the arithmetic core: its
purpose is to prove that the five ZMM results are written to the correct SysV
output rows without cross-row corruption. Input-load and complete ABI
composition remain separate obligations.
-/

import NaryaFormal.X86Refinement

namespace NaryaFormal.X86

def outputRowAddress {Other : Type} (state : MachineState Other)
    (limb : Fin 5) : Addr :=
  addressAdd (state.gpr .rdi) (64 * limb.val)

def outputRegister (limb : Fin 5) : ZReg :=
  ⟨10 + limb.val, by omega⟩

def storedR51OutputState {Other : Type} (state : MachineState Other) :
    MachineState Other :=
  let s0 := vmovdqu64Store state (addressAdd (state.gpr .rdi) 0) 10
  let s1 := vmovdqu64Store s0 (addressAdd (state.gpr .rdi) 64) 11
  let s2 := vmovdqu64Store s1 (addressAdd (state.gpr .rdi) 128) 12
  let s3 := vmovdqu64Store s2 (addressAdd (state.gpr .rdi) 192) 13
  vmovdqu64Store s3 (addressAdd (state.gpr .rdi) 256) 14

def outputWrittenAddresses {Other : Type} (state : MachineState Other) :
    List Addr :=
  zmmWrittenAddresses (addressAdd (state.gpr .rdi) 0) (state.zmm 10) ++
  zmmWrittenAddresses (addressAdd (state.gpr .rdi) 64) (state.zmm 11) ++
  zmmWrittenAddresses (addressAdd (state.gpr .rdi) 128) (state.zmm 12) ++
  zmmWrittenAddresses (addressAdd (state.gpr .rdi) 192) (state.zmm 13) ++
  zmmWrittenAddresses (addressAdd (state.gpr .rdi) 256) (state.zmm 14)

/-- The ABI-forbidden overlap: an output row may not cover the return slot. -/
def stackOutputRowsDisjoint {Other : Type} (state : MachineState Other) : Prop :=
  ∀ limb : Fin 5,
    qwordZmmRangesDisjoint (state.gpr .rsp) (outputRowAddress state limb)

/-- Every written output row reads back the exact source ZMM. -/
theorem stored_output_rows_exact {Other : Type}
    (state : MachineState Other) (limb : Fin 5) :
    loadZmm (storedR51OutputState state).mem (outputRowAddress state limb) =
      state.zmm (outputRegister limb) := by
  fin_cases limb <;>
    simp only [storedR51OutputState, outputRowAddress, outputRegister,
      vmovdqu64Store] <;>
    repeat' first
      | rw [loadZmm_storeZmm_same]
      | rw [loadZmm_storeZmm_offset_disjoint] <;> norm_num
  all_goals apply congrArg state.zmm; apply Fin.ext; rfl

theorem stored_output_permissions_preserved {Other : Type}
    (state : MachineState Other) :
    (storedR51OutputState state).mem.perm = state.mem.perm := by
  simp only [storedR51OutputState, vmovdqu64Store]
  repeat' rw [storeZmm_permissions]

/-- No byte outside the five exact 64-byte output rows is modified. -/
theorem stored_output_frame {Other : Type} (state : MachineState Other)
    (candidate : Addr)
    (hnot : candidate ∉ outputWrittenAddresses state) :
    (storedR51OutputState state).mem.byte candidate =
      state.mem.byte candidate := by
  simp only [outputWrittenAddresses, List.mem_append, not_or] at hnot
  rcases hnot with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
  simp only [storedR51OutputState, vmovdqu64Store]
  rw [storeZmm_frame _ _ _ _ h4]
  rw [storeZmm_frame _ _ _ _ h3]
  rw [storeZmm_frame _ _ _ _ h2]
  rw [storeZmm_frame _ _ _ _ h1]
  rw [storeZmm_frame _ _ _ _ h0]

theorem stored_output_registers_preserved {Other : Type}
    (state : MachineState Other) :
    (storedR51OutputState state).gpr = state.gpr ∧
      (storedR51OutputState state).zmm = state.zmm ∧
      (storedR51OutputState state).opmask = state.opmask := by
  simp only [storedR51OutputState, vmovdqu64Store]
  exact ⟨True.intro, True.intro, True.intro⟩

theorem stored_output_return_readability {Other : Type}
    (state : MachineState Other) :
    readableBytes (storedR51OutputState state).mem (state.gpr .rsp) 8 =
      readableBytes state.mem (state.gpr .rsp) 8 := by
  unfold readableBytes
  rw [stored_output_permissions_preserved]

/-- Five output rows preserve a disjoint eight-byte stack return word. -/
theorem stored_output_return_word {Other : Type} (state : MachineState Other)
    (hdisjoint : stackOutputRowsDisjoint state) :
    loadQwordLE (storedR51OutputState state).mem (state.gpr .rsp) =
      loadQwordLE state.mem (state.gpr .rsp) := by
  have h0 : qwordZmmRangesDisjoint (state.gpr .rsp)
      (addressAdd (state.gpr .rdi) 0) := by
    simpa [outputRowAddress] using hdisjoint 0
  have h1 : qwordZmmRangesDisjoint (state.gpr .rsp)
      (addressAdd (state.gpr .rdi) 64) := by
    simpa [outputRowAddress] using hdisjoint 1
  have h2 : qwordZmmRangesDisjoint (state.gpr .rsp)
      (addressAdd (state.gpr .rdi) 128) := by
    simpa [outputRowAddress] using hdisjoint 2
  have h3 : qwordZmmRangesDisjoint (state.gpr .rsp)
      (addressAdd (state.gpr .rdi) 192) := by
    simpa [outputRowAddress] using hdisjoint 3
  have h4 : qwordZmmRangesDisjoint (state.gpr .rsp)
      (addressAdd (state.gpr .rdi) 256) := by
    simpa [outputRowAddress] using hdisjoint 4
  simp only [storedR51OutputState, vmovdqu64Store]
  rw [loadQwordLE_storeZmm_disjoint _ _ _ _ h4]
  rw [loadQwordLE_storeZmm_disjoint _ _ _ _ h3]
  rw [loadQwordLE_storeZmm_disjoint _ _ _ _ h2]
  rw [loadQwordLE_storeZmm_disjoint _ _ _ _ h1]
  rw [loadQwordLE_storeZmm_disjoint _ _ _ _ h0]

/-- The exact decoded five-store phase succeeds under explicit row permissions. -/
theorem run_store_phase {Other : Type} (state : MachineState Other)
    (hwrite : ∀ limb : Fin 5,
      writableBytes state.mem (outputRowAddress state limb) 64 = true) :
    runMachinePhase GeneratedR51InstructionTrace.storePhase state =
      .ok (storedR51OutputState state) := by
  have h0 := hwrite (0 : Fin 5)
  have h1 := hwrite (1 : Fin 5)
  have h2 := hwrite (2 : Fin 5)
  have h3 := hwrite (3 : Fin 5)
  have h4 := hwrite (4 : Fin 5)
  norm_num [outputRowAddress] at h0 h1 h2 h3 h4
  let s0 := vmovdqu64Store state (addressAdd (state.gpr .rdi) 0) 10
  let s1 := vmovdqu64Store s0 (addressAdd (s0.gpr .rdi) 64) 11
  let s2 := vmovdqu64Store s1 (addressAdd (s1.gpr .rdi) 128) 12
  let s3 := vmovdqu64Store s2 (addressAdd (s2.gpr .rdi) 192) 13
  let s4 := vmovdqu64Store s3 (addressAdd (s3.gpr .rdi) 256) 14
  have hwrite1 : writableBytes s0.mem
      (addressAdd (s0.gpr .rdi) 64) 64 = true := by
    simpa [s0, vmovdqu64Store, writableBytes_storeZmm] using h1
  have hwrite2 : writableBytes s1.mem
      (addressAdd (s1.gpr .rdi) 128) 64 = true := by
    simpa [s1, s0, vmovdqu64Store, writableBytes_storeZmm] using h2
  have hwrite3 : writableBytes s2.mem
      (addressAdd (s2.gpr .rdi) 192) 64 = true := by
    simpa [s2, s1, s0, vmovdqu64Store, writableBytes_storeZmm] using h3
  have hwrite4 : writableBytes s3.mem
      (addressAdd (s3.gpr .rdi) 256) 64 = true := by
    simpa [s3, s2, s1, s0, vmovdqu64Store, writableBytes_storeZmm] using h4
  have hexec0 : executeInstruction (.vmovdqu64Store .rdi 0 10) state =
      .ok (.next s0) := by
    change (execVmovdqu64Store state _ _).map _ = _
    rw [execVmovdqu64Store_writable state _ _ h0]
    rfl
  have hexec1 : executeInstruction (.vmovdqu64Store .rdi 64 11) s0 =
      .ok (.next s1) := by
    change (execVmovdqu64Store s0 _ _).map _ = _
    rw [execVmovdqu64Store_writable s0 _ _ hwrite1]
    rfl
  have hexec2 : executeInstruction (.vmovdqu64Store .rdi 128 12) s1 =
      .ok (.next s2) := by
    change (execVmovdqu64Store s1 _ _).map _ = _
    rw [execVmovdqu64Store_writable s1 _ _ hwrite2]
    rfl
  have hexec3 : executeInstruction (.vmovdqu64Store .rdi 192 13) s2 =
      .ok (.next s3) := by
    change (execVmovdqu64Store s2 _ _).map _ = _
    rw [execVmovdqu64Store_writable s2 _ _ hwrite3]
    rfl
  have hexec4 : executeInstruction (.vmovdqu64Store .rdi 256 14) s3 =
      .ok (.next s4) := by
    change (execVmovdqu64Store s3 _ _).map _ = _
    rw [execVmovdqu64Store_writable s3 _ _ hwrite4]
    rfl
  simp [GeneratedR51InstructionTrace.storePhase, runMachinePhase,
    hexec0, hexec1, hexec2, hexec3, hexec4]
  rfl

theorem normalized_output_register (environment : NatShadowEnvironment)
    (limb : Fin 5) :
    (normalizedNatShadowState environment).zmm (outputRegister limb) =
      (storedNatShadowState environment).output limb := by
  fin_cases limb <;>
    rfl

/--
The machine store suffix writes the mathematical multiplier output for the
selected SIMD lane. This closes the output-memory part of the leaf once a
post-arithmetic `laneAgrees` witness has been established.
-/
theorem run_store_phase_refines {Other : Type}
    (environment : NatShadowEnvironment) (lane : Fin 8)
    (state : MachineState Other)
    (hagrees : laneAgrees lane state (normalizedNatShadowState environment))
    (hwrite : ∀ limb : Fin 5,
      writableBytes state.mem (outputRowAddress state limb) 64 = true) :
    ∃ next,
      runMachinePhase GeneratedR51InstructionTrace.storePhase state = .ok next ∧
      (∀ limb : Fin 5,
        (loadZmm next.mem (outputRowAddress state limb) lane).toNat =
          (storedNatShadowState environment).output limb) ∧
      next.mem.perm = state.mem.perm ∧
      next.gpr = state.gpr ∧ next.zmm = state.zmm ∧
      (∀ candidate, candidate ∉ outputWrittenAddresses state →
        next.mem.byte candidate = state.mem.byte candidate) := by
  refine ⟨storedR51OutputState state, run_store_phase state hwrite, ?_,
    stored_output_permissions_preserved state,
    (stored_output_registers_preserved state).1,
    (stored_output_registers_preserved state).2.1,
    stored_output_frame state⟩
  intro limb
  rw [stored_output_rows_exact state limb]
  rw [hagrees (outputRegister limb)]
  exact normalized_output_register environment limb

end NaryaFormal.X86
