/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Symbolic executor for straight-line AVX-512 IFMA field leaves.

Each defined ZMM register carries, for one arbitrary selected lane, an exact
unbounded-natural expression over the entry-memory input rows together with an
inclusive upper bound on that expression. The executor is partial: it returns
`none` whenever it cannot justify an instruction, in particular whenever the
tracked bounds do not rule out 64-bit wraparound or an IFMA operand of more
than 52 bits.

This file is a definition of the checker only. Its link to the byte-addressed
machine model is `executeSym_sound` in `X86IfmaSoundness.lean`.
-/

import NaryaFormal.X86Execution

namespace NaryaFormal.IfmaSym

open NaryaFormal.X86

/-- Unbounded-natural value of one selected qword lane. `input base
displacement` is that lane of the 64-byte row at `base + displacement` in entry
memory. -/
inductive Expr
  | input (base : Gpr) (displacement : Nat)
  | const (value : Nat)
  | add (left right : Expr)
  | mul (left right : Expr)
  | mulLo52 (left right : Expr)
  | mulHi52 (left right : Expr)
  | shiftLeft (operand : Expr) (amount : Nat)
  | shiftRight (operand : Expr) (amount : Nat)
  | modPow2 (operand : Expr) (bits : Nat)
  deriving DecidableEq, Repr

def Expr.eval (inputs : Gpr → Nat → Nat) : Expr → Nat
  | .input base displacement => inputs base displacement
  | .const value => value
  | .add left right => left.eval inputs + right.eval inputs
  | .mul left right => left.eval inputs * right.eval inputs
  | .mulLo52 left right => (left.eval inputs * right.eval inputs) % 2 ^ 52
  | .mulHi52 left right => (left.eval inputs * right.eval inputs) / 2 ^ 52
  | .shiftLeft operand amount => operand.eval inputs * 2 ^ amount
  | .shiftRight operand amount => operand.eval inputs / 2 ^ amount
  | .modPow2 operand bits => operand.eval inputs % 2 ^ bits

/-- An expression with an inclusive upper bound on its value. -/
structure SymVal where
  expr : Expr
  bound : Nat
  deriving DecidableEq, Repr

/-- One readable 64-byte input row and the bound assumed for every lane the
theorem is instantiated at. -/
structure InputRow where
  base : Gpr
  displacement : Nat
  bound : Nat
  deriving DecidableEq, Repr

/-- One read-only qword constant at an absolute address. -/
structure Constant where
  address : Nat
  value : Nat
  deriving DecidableEq, Repr

structure LeafSpec where
  inputs : List InputRow
  constants : List Constant
  /-- Register holding the output object pointer at entry. -/
  outputBase : Gpr
  /-- Exact byte length of the output object. -/
  outputBytes : Nat
  deriving DecidableEq, Repr

structure SymState where
  /-- `none` is an undefined register: reading it is rejected. -/
  zmm : ZReg → Option SymVal
  /-- Rows stored so far, keyed by displacement from the output pointer. -/
  output : Nat → Option SymVal
  /-- Set by the first store. Loads and constant broadcasts are rejected
  afterwards, so inputs may overlap the output object arbitrarily. -/
  stored : Bool


def initialSymState : SymState :=
  { zmm := fun _ => none, output := fun _ => none, stored := false }


def setSymZmm (registers : ZReg → Option SymVal) (target : ZReg)
    (value : SymVal) : ZReg → Option SymVal :=
  fun register => if register = target then some value else registers register


def setSymOutput (output : Nat → Option SymVal) (displacement : Nat)
    (value : SymVal) : Nat → Option SymVal :=
  fun candidate => if candidate = displacement then some value else output candidate


def writeSym (state : SymState) (target : ZReg) (value : SymVal) : SymState :=
  { state with zmm := setSymZmm state.zmm target value }


def findInput (spec : LeafSpec) (base : Gpr) (displacement : Nat) :
    Option InputRow :=
  spec.inputs.find? (fun row => row.base = base ∧ row.displacement = displacement)


def findConstant (spec : LeafSpec) (address : Nat) : Option Constant :=
  spec.constants.find? (fun constant => constant.address = address)


/-- `some bits` exactly when `mask = 2^bits - 1` for some `bits ≤ 64`. A plain
bounded search keeps the checker evaluable by kernel reduction. -/
def maskBits (mask : Nat) : Option Nat :=
  (List.range 65).find? (fun bits => mask + 1 = 2 ^ bits)


def executeSym (spec : LeafSpec) (instruction : Instruction)
    (state : SymState) : Option SymState :=
  match instruction with
  | .vmovdqu64Load destination base displacement =>
      if state.stored = false then
        match findInput spec base displacement with
        | some row =>
            some (writeSym state destination
              ⟨.input base displacement, row.bound⟩)
        | none => none
      else none
  | .vmovdqu64Store base displacement source =>
      match state.zmm source with
      | some value =>
          if base = spec.outputBase ∧ displacement % 64 = 0 ∧
              displacement + 64 ≤ spec.outputBytes then
            some { state with
              output := setSymOutput state.output displacement value
              stored := true }
          else none
      | none => none
  | .vpxorq destination source1 source2 =>
      -- Only the zeroing idiom is supported; it defines an undefined register.
      if source1 = source2 then
        some (writeSym state destination ⟨.const 0, 0⟩)
      else none
  | .vpmadd52luq destination source1 source2 =>
      match state.zmm destination, state.zmm source1, state.zmm source2 with
      | some accumulator, some left, some right =>
          let product := min (2 ^ 52 - 1) (left.bound * right.bound)
          if left.bound < 2 ^ 52 ∧ right.bound < 2 ^ 52 ∧
              accumulator.bound + product < 2 ^ 64 then
            some (writeSym state destination
              ⟨.add accumulator.expr (.mulLo52 left.expr right.expr),
                accumulator.bound + product⟩)
          else none
      | _, _, _ => none
  | .vpmadd52huq destination source1 source2 =>
      match state.zmm destination, state.zmm source1, state.zmm source2 with
      | some accumulator, some left, some right =>
          let product := left.bound * right.bound / 2 ^ 52
          if left.bound < 2 ^ 52 ∧ right.bound < 2 ^ 52 ∧
              accumulator.bound + product < 2 ^ 64 then
            some (writeSym state destination
              ⟨.add accumulator.expr (.mulHi52 left.expr right.expr),
                accumulator.bound + product⟩)
          else none
      | _, _, _ => none
  | .vpaddq destination source1 source2 =>
      match state.zmm source1, state.zmm source2 with
      | some left, some right =>
          if left.bound + right.bound < 2 ^ 64 then
            some (writeSym state destination
              ⟨.add left.expr right.expr, left.bound + right.bound⟩)
          else none
      | _, _ => none
  | .vpmullq destination source1 source2 =>
      match state.zmm source1, state.zmm source2 with
      | some left, some right =>
          if left.bound * right.bound < 2 ^ 64 then
            some (writeSym state destination
              ⟨.mul left.expr right.expr, left.bound * right.bound⟩)
          else none
      | _, _ => none
  | .vpandq destination source1 source2 =>
      -- Only AND with a constant low-bit mask `2^bits - 1` is supported.
      match state.zmm source1, state.zmm source2 with
      | some left, some ⟨.const mask, _⟩ =>
          match maskBits mask with
          | some bits =>
              some (writeSym state destination
                ⟨.modPow2 left.expr bits, min left.bound mask⟩)
          | none => none
      | _, _ => none
  | .vpsllq destination source amount =>
      match state.zmm source with
      | some operand =>
          if operand.bound * 2 ^ amount < 2 ^ 64 then
            some (writeSym state destination
              ⟨.shiftLeft operand.expr amount, operand.bound * 2 ^ amount⟩)
          else none
      | none => none
  | .vpsrlq destination source amount =>
      match state.zmm source with
      | some operand =>
          some (writeSym state destination
            ⟨.shiftRight operand.expr amount, operand.bound / 2 ^ amount⟩)
      | none => none
  | .vpbroadcastq destination absoluteAddress =>
      if state.stored = false then
        match findConstant spec absoluteAddress with
        | some constant =>
            some (writeSym state destination
              ⟨.const constant.value, constant.value⟩)
        | none => none
      else none
  | .vzeroUpper => none
  | .ret => none


def runSym (spec : LeafSpec) : List Instruction → SymState → Option SymState
  | [], state => some state
  | instruction :: rest, state =>
      match executeSym spec instruction state with
      | some next => runSym spec rest next
      | none => none


/-- Expression stored at an output displacement, or a constant zero if the
row was never stored. Use together with `outputBound`, which is `2^64` for a
missing row and therefore fails every useful bound check. -/
def outputExpr (state : SymState) (displacement : Nat) : Expr :=
  match state.output displacement with
  | some value => value.expr
  | none => .const 0


def outputBound (state : SymState) (displacement : Nat) : Nat :=
  match state.output displacement with
  | some value => value.bound
  | none => 2 ^ 64


def outputDefined (state : SymState) (displacement : Nat) : Bool :=
  (state.output displacement).isSome


theorem eq_some_getD_of_isSome {α : Type} (value : Option α) (fallback : α)
    (hsome : value.isSome = true) : value = some (value.getD fallback) := by
  cases value with
  | none => cases hsome
  | some _ => rfl


open Lean Elab Term Meta in
/-- `reduced% t` elaborates the closed term `t` and returns its normal form.
It is used only to write down the constructor form of a checker result. The
elaborator is not trusted: every use is paired with a kernel-checked equation
between `t` and the returned term. -/
elab "reduced% " t:term : term => do
  let e ← elabTerm t none
  let e ← instantiateMVars e
  reduce e (skipProofs := true) (skipTypes := true)

end NaryaFormal.IfmaSym
