/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Unbounded-natural shadow interpreter for one SIMD lane of the restricted r51
multiplier program. This interpreter deliberately omits machine wrapping. Its
IFMA operations use the mathematical split on operands that the later
machine-refinement theorem must prove are u52 at each program point.
-/

import NaryaFormal.AssemblyTrace
import NaryaFormal.X86Execution

namespace NaryaFormal.X86

open Radix51

structure NatShadowEnvironment where
  x : FiveLimbs
  y : FiveLimbs

structure NatShadowState where
  zmm : ZReg → Nat
  output : Fin 5 → Nat

inductive NatShadowOutcome
  | next (state : NatShadowState)
  | returned (state : NatShadowState)

def setNatZmm (registers : ZReg → Nat) (target : ZReg) (value : Nat) :
    ZReg → Nat :=
  fun register => if register = target then value else registers register

def setNatOutput (output : Fin 5 → Nat) (target : Fin 5) (value : Nat) :
    Fin 5 → Nat :=
  fun limb => if limb = target then value else output limb

def shadowLimbIndex (displacement : Nat) : Option (Fin 5) :=
  if displacement % 64 = 0 then
    let index := displacement / 64
    if hindex : index < 5 then some ⟨index, hindex⟩ else none
  else none

def shadowLoad (environment : NatShadowEnvironment) (base : Gpr)
    (displacement : Nat) : Option Nat := do
  let limb ← shadowLimbIndex displacement
  match base with
  | .rsi => some (environment.x limb)
  | .rdx => some (environment.y limb)
  | _ => none

def shadowConstant (absoluteAddress : Nat) : Option Nat :=
  if absoluteAddress = R51Object.ifma_fold19Address then some 19
  else if absoluteAddress = R51Object.ifma_mask51Address then some (2 ^ 51 - 1)
  else none

def writeNatZmm (state : NatShadowState) (target : ZReg) (value : Nat) :
    NatShadowState :=
  { state with zmm := setNatZmm state.zmm target value }

def executeNatShadow (environment : NatShadowEnvironment)
    (instruction : Instruction) (state : NatShadowState) :
    Option NatShadowOutcome :=
  match instruction with
  | .vmovdqu64Load destination base displacement => do
      let value ← shadowLoad environment base displacement
      some (.next (writeNatZmm state destination value))
  | .vmovdqu64Store base displacement source =>
      if base ≠ .rdi then none else do
      let limb ← shadowLimbIndex displacement
      some (.next { state with
        output := setNatOutput state.output limb (state.zmm source) })
  | .vpxorq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 ^^^ state.zmm source2)))
  | .vpmadd52luq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm destination + lo52 (state.zmm source1) (state.zmm source2))))
  | .vpmadd52huq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm destination + hi52 (state.zmm source1) (state.zmm source2))))
  | .vpaddq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 + state.zmm source2)))
  | .vpmullq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 * state.zmm source2)))
  | .vpandq destination source1 source2 =>
      some (.next (writeNatZmm state destination
        (state.zmm source1 &&& state.zmm source2)))
  | .vpsllq destination source amount =>
      some (.next (writeNatZmm state destination
        (state.zmm source * 2 ^ amount)))
  | .vpsrlq destination source amount =>
      some (.next (writeNatZmm state destination
        (state.zmm source / 2 ^ amount)))
  | .vpbroadcastq destination absoluteAddress => do
      let value ← shadowConstant absoluteAddress
      some (.next (writeNatZmm state destination value))
  | .vzeroUpper => some (.next state)
  | .ret => some (.returned state)

def runNatShadow (environment : NatShadowEnvironment) :
    List Instruction → NatShadowState → Option NatShadowOutcome
  | [], _ => none
  | instruction :: rest, state => do
      let outcome ← executeNatShadow environment instruction state
      match outcome with
      | .next nextState => runNatShadow environment rest nextState
      | .returned returnState =>
          if rest.isEmpty then some (.returned returnState) else none

def initialNatShadowState : NatShadowState :=
  { zmm := fun _ => 0
    output := fun _ => 0 }

def natShadowOutput (state : NatShadowState) : Loose5 :=
  { l0 := state.output 0
    l1 := state.output 1
    l2 := state.output 2
    l3 := state.output 3
    l4 := state.output 4 }

def runR51NatShadow (x y : FiveLimbs) : Option Loose5 := do
  let outcome ← runNatShadow { x, y }
    GeneratedR51InstructionTrace.expectedProgram initialNatShadowState
  match outcome with
  | .returned state => some (natShadowOutput state)
  | .next _ => none

theorem and_mask51_eq_mod (value : Nat) :
    value &&& 2251799813685247 = value % 2251799813685248 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod value 51

end NaryaFormal.X86
