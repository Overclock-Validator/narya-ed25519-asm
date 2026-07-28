/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Local machine-to-natural refinement lemmas for one SIMD lane. These lemmas
make every no-wrap/u52 premise explicit. The remaining whole-program theorem
must discharge those premises from the source-linked range certificate.
-/

import NaryaFormal.X86NatShadow

namespace NaryaFormal.X86

def laneAgrees {Other : Type} (lane : Fin 8) (machine : MachineState Other)
    (shadow : NatShadowState) : Prop :=
  ∀ register, (machine.zmm register lane).toNat = shadow.zmm register

theorem laneAgrees_write {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (target : ZReg) (machineValue : Zmm) (shadowValue : Nat)
    (hagrees : laneAgrees lane machine shadow)
    (hvalue : (machineValue lane).toNat = shadowValue) :
    laneAgrees lane (writeZmm machine target machineValue)
      (writeNatZmm shadow target shadowValue) := by
  intro register
  by_cases hregister : register = target
  · subst register
    simpa [writeZmm, writeNatZmm, setZmm, setNatZmm] using hvalue
  · simpa [writeZmm, writeNatZmm, setZmm, setNatZmm, hregister]
      using hagrees register

theorem refine_vpxorq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow) :
    laneAgrees lane
      (writeZmm machine destination
        (vpxorq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 ^^^ shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  simp [vpxorq, laneMap2, qwordXor, hagrees source1, hagrees source2]

theorem refine_vpandq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow) :
    laneAgrees lane
      (writeZmm machine destination
        (vpandq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 &&& shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  simp [vpandq, laneMap2, qwordAnd, hagrees source1, hagrees source2]

theorem refine_vpaddq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hnoWrap : shadow.zmm source1 + shadow.zmm source2 < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpaddq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 + shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordAdd (machine.zmm source1 lane)
    (machine.zmm source2 lane)).toNat = _
  rw [qwordAdd_toNat_of_noWrap]
  · rw [hagrees source1, hagrees source2]
  · simpa [hagrees source1, hagrees source2] using hnoWrap

theorem refine_vpmullq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hnoWrap : shadow.zmm source1 * shadow.zmm source2 < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpmullq (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm source1 * shadow.zmm source2)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordMul (machine.zmm source1 lane)
    (machine.zmm source2 lane)).toNat = _
  rw [qwordMul_toNat_of_noWrap]
  · rw [hagrees source1, hagrees source2]
  · simpa [hagrees source1, hagrees source2] using hnoWrap

theorem refine_vpsllq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source : ZReg) (amount : Nat)
    (hagrees : laneAgrees lane machine shadow)
    (hnoWrap : shadow.zmm source * 2 ^ amount < U64) :
    laneAgrees lane
      (writeZmm machine destination (vpsllq (machine.zmm source) amount))
      (writeNatZmm shadow destination (shadow.zmm source * 2 ^ amount)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordShiftLeft (machine.zmm source lane) amount).toNat = _
  rw [qwordShiftLeft_toNat_of_noWrap]
  · rw [hagrees source]
  · simpa [hagrees source] using hnoWrap

theorem refine_vpsrlq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source : ZReg) (amount : Nat)
    (hagrees : laneAgrees lane machine shadow) :
    laneAgrees lane
      (writeZmm machine destination (vpsrlq (machine.zmm source) amount))
      (writeNatZmm shadow destination (shadow.zmm source / 2 ^ amount)) := by
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (qwordShiftRight (machine.zmm source lane) amount).toNat = _
  rw [qwordShiftRight_toNat, hagrees source]

theorem refine_vpmadd52luq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hsource1 : shadow.zmm source1 < U52)
    (hsource2 : shadow.zmm source2 < U52)
    (hnoWrap : shadow.zmm destination +
      Radix51.lo52 (shadow.zmm source1) (shadow.zmm source2) < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpmadd52luq (machine.zmm destination)
          (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm destination +
          Radix51.lo52 (shadow.zmm source1) (shadow.zmm source2))) := by
  have hm1 : (machine.zmm source1 lane).toNat < U52 := by
    simpa [hagrees source1] using hsource1
  have hm2 : (machine.zmm source2 lane).toNat < U52 := by
    simpa [hagrees source2] using hsource2
  have hlo : ifmaLo52 (machine.zmm source1 lane) (machine.zmm source2 lane) =
      Radix51.lo52 (shadow.zmm source1) (shadow.zmm source2) := by
    rw [ifmaLo52_eq_of_u52 _ _ hm1 hm2]
    simp [Radix51.lo52, Radix51.U52, U52, hagrees source1, hagrees source2]
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (vpmadd52luqLane (machine.zmm destination lane)
    (machine.zmm source1 lane) (machine.zmm source2 lane)).toNat = _
  rw [vpmadd52luqLane_toNat_of_noWrap]
  · rw [hagrees destination, hlo]
  · simpa [hagrees destination, hlo] using hnoWrap

theorem refine_vpmadd52huq {Other : Type} (lane : Fin 8)
    (machine : MachineState Other) (shadow : NatShadowState)
    (destination source1 source2 : ZReg)
    (hagrees : laneAgrees lane machine shadow)
    (hsource1 : shadow.zmm source1 < U52)
    (hsource2 : shadow.zmm source2 < U52)
    (hnoWrap : shadow.zmm destination +
      Radix51.hi52 (shadow.zmm source1) (shadow.zmm source2) < U64) :
    laneAgrees lane
      (writeZmm machine destination
        (vpmadd52huq (machine.zmm destination)
          (machine.zmm source1) (machine.zmm source2)))
      (writeNatZmm shadow destination
        (shadow.zmm destination +
          Radix51.hi52 (shadow.zmm source1) (shadow.zmm source2))) := by
  have hm1 : (machine.zmm source1 lane).toNat < U52 := by
    simpa [hagrees source1] using hsource1
  have hm2 : (machine.zmm source2 lane).toNat < U52 := by
    simpa [hagrees source2] using hsource2
  have hhi : ifmaHi52 (machine.zmm source1 lane) (machine.zmm source2 lane) =
      Radix51.hi52 (shadow.zmm source1) (shadow.zmm source2) := by
    rw [ifmaHi52_eq_of_u52 _ _ hm1 hm2]
    simp [Radix51.hi52, Radix51.U52, U52, hagrees source1, hagrees source2]
  apply laneAgrees_write lane machine shadow destination _ _ hagrees
  change (vpmadd52huqLane (machine.zmm destination lane)
    (machine.zmm source1 lane) (machine.zmm source2 lane)).toNat = _
  rw [vpmadd52huqLane_toNat_of_noWrap]
  · rw [hagrees destination, hhi]
  · simpa [hagrees destination, hhi] using hnoWrap

end NaryaFormal.X86
