/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Link-layout independence of the IFMA checker.

A linked leaf refers to its read-only constants by absolute address, so the
decoded instruction list of the same code differs between two binaries only in
the addresses carried by `vpbroadcastq`. This file shows the checker's result
is unchanged when those addresses are renamed consistently in the program and
in the leaf specification.
-/

import NaryaFormal.X86IfmaSoundness

namespace NaryaFormal.IfmaSym

open NaryaFormal.X86

def relocateInstruction (rename : Nat → Nat) : Instruction → Instruction
  | .vpbroadcastq destination absoluteAddress =>
      .vpbroadcastq destination (rename absoluteAddress)
  | instruction => instruction


def relocateConstant (rename : Nat → Nat) (constant : Constant) : Constant :=
  { constant with address := rename constant.address }


def relocateSpec (rename : Nat → Nat) (spec : LeafSpec) : LeafSpec :=
  { spec with constants := spec.constants.map (relocateConstant rename) }


/-- Addresses read by constant broadcasts in a program. -/
def broadcastAddresses : List Instruction → List Nat
  | [] => []
  | .vpbroadcastq _ absoluteAddress :: rest =>
      absoluteAddress :: broadcastAddresses rest
  | _ :: rest => broadcastAddresses rest


/-- `rename` does not confuse a declared constant with a broadcast address. -/
def RenameFaithful (rename : Nat → Nat) (spec : LeafSpec)
    (addresses : List Nat) : Prop :=
  ∀ constant ∈ spec.constants, ∀ address ∈ addresses,
    rename constant.address = rename address → constant.address = address


theorem find_relocate (rename : Nat → Nat) (address : Nat) :
    ∀ constants : List Constant,
      (∀ constant ∈ constants,
        rename constant.address = rename address → constant.address = address) →
      (constants.map (relocateConstant rename)).find?
          (fun constant => constant.address = rename address) =
        (constants.find? (fun constant => constant.address = address)).map
          (relocateConstant rename)
  | [], _ => rfl
  | head :: tail, hfaithful => by
      have ih := find_relocate rename address tail
        (fun constant hmember =>
          hfaithful constant (List.mem_cons_of_mem _ hmember))
      by_cases hhead : head.address = address
      · simp [relocateConstant, hhead]
      · have hrenamed : rename head.address ≠ rename address := fun hequal =>
          hhead (hfaithful head (List.mem_cons_self ..) hequal)
        simpa [relocateConstant, hhead, hrenamed] using ih


theorem findConstant_relocate (rename : Nat → Nat) (spec : LeafSpec)
    (address : Nat)
    (hfaithful : ∀ constant ∈ spec.constants,
      rename constant.address = rename address → constant.address = address) :
    findConstant (relocateSpec rename spec) (rename address) =
      (findConstant spec address).map (relocateConstant rename) :=
  find_relocate rename address spec.constants hfaithful


theorem executeSym_relocate (rename : Nat → Nat) (spec : LeafSpec)
    (instruction : Instruction) (state : SymState)
    (hfaithful : RenameFaithful rename spec (broadcastAddresses [instruction])) :
    executeSym (relocateSpec rename spec)
        (relocateInstruction rename instruction) state =
      executeSym spec instruction state := by
  cases instruction with
  | vpbroadcastq destination absoluteAddress =>
      have hfind := findConstant_relocate rename spec absoluteAddress
        (fun constant hmember =>
          hfaithful constant hmember absoluteAddress (by simp [broadcastAddresses]))
      simp only [relocateInstruction, executeSym, hfind]
      cases findConstant spec absoluteAddress <;> rfl
  | _ => rfl


/-- The checker's whole-body result is independent of where the constants are
linked. -/
theorem runSym_relocate (rename : Nat → Nat) (spec : LeafSpec)
    (program : List Instruction) (state : SymState)
    (hfaithful : RenameFaithful rename spec (broadcastAddresses program)) :
    runSym (relocateSpec rename spec)
        (program.map (relocateInstruction rename)) state =
      runSym spec program state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      have hhead : RenameFaithful rename spec
          (broadcastAddresses [instruction]) := by
        intro constant hmember address haddress
        apply hfaithful constant hmember address
        cases instruction <;> simp_all [broadcastAddresses]
      have htail : RenameFaithful rename spec (broadcastAddresses rest) := by
        intro constant hmember address haddress
        apply hfaithful constant hmember address
        cases instruction <;> simp_all [broadcastAddresses]
      simp only [List.map_cons, runSym, executeSym_relocate rename spec
        instruction state hhead]
      cases executeSym spec instruction state with
      | none => rfl
      | some next => exact ih next htail

end NaryaFormal.IfmaSym
