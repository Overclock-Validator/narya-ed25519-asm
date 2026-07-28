/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Restricted decoder and semantics for the eight-instruction YMM shuffle block
used by both transpose leaves. This module deliberately does not decode the
surrounding GPR or memory instructions yet. It closes the highest-risk emitted
opcode question: every assembled shuffle block decodes to the exact register
schedule whose lane permutation is proved in Transpose.lean.
-/

import NaryaFormal.Transpose
import NaryaFormal.TransposeObjectBytes
import NaryaFormal.X86Decoder

namespace NaryaFormal.TransposeX86

open NaryaFormal.Transpose

universe u

variable {α : Type u}

abbrev YReg := Fin 8

inductive Instruction
  | unpackLow (destination source1 source2 : YReg)
  | unpackHigh (destination source1 source2 : YReg)
  | shuffleI64x2 (destination source1 source2 : YReg) (immediate : Nat)
  deriving DecidableEq, Repr

def yregOfNat (value : Nat) : Option YReg :=
  if hvalue : value < 8 then some ⟨value, hvalue⟩ else none

/-- Decode the VEX.256 `VPUNPCKLQDQ/HQDQ` register forms used by the leaves. -/
def decodeUnpack (bytes : List Nat) (offset : Nat) :
    Option (Instruction × Nat) := do
  let marker ← NaryaFormal.X86.byteAt bytes offset
  let vex ← NaryaFormal.X86.byteAt bytes (offset + 1)
  let opcode ← NaryaFormal.X86.byteAt bytes (offset + 2)
  let modrm ← NaryaFormal.X86.byteAt bytes (offset + 3)
  if marker ≠ 0xc5 || vex.testBit 7 = false || vex % 8 ≠ 5 ||
      NaryaFormal.X86.bitField modrm 6 2 ≠ 3 then none else
  let destination ← yregOfNat (NaryaFormal.X86.bitField modrm 3 3)
  let source1 ← yregOfNat (15 - NaryaFormal.X86.bitField vex 3 4)
  let source2 ← yregOfNat (NaryaFormal.X86.bitField modrm 0 3)
  let instruction ←
    match opcode with
    | 0x6c => some (.unpackLow destination source1 source2)
    | 0x6d => some (.unpackHigh destination source1 source2)
    | _ => none
  some (instruction, offset + 4)

/-- Decode the EVEX.256 `VSHUFI64X2` register form used by the leaves. -/
def decodeShuffle (bytes : List Nat) (offset : Nat) :
    Option (Instruction × Nat) := do
  let marker ← NaryaFormal.X86.byteAt bytes offset
  let p0 ← NaryaFormal.X86.byteAt bytes (offset + 1)
  let p1 ← NaryaFormal.X86.byteAt bytes (offset + 2)
  let p2 ← NaryaFormal.X86.byteAt bytes (offset + 3)
  let opcode ← NaryaFormal.X86.byteAt bytes (offset + 4)
  let modrm ← NaryaFormal.X86.byteAt bytes (offset + 5)
  let immediate ← NaryaFormal.X86.byteAt bytes (offset + 6)
  if marker ≠ 0x62 || p0 ≠ 0xf3 || p2 ≠ 0x28 || opcode ≠ 0x43 ||
      p1.testBit 7 = false || p1 % 8 ≠ 5 ||
      NaryaFormal.X86.bitField modrm 6 2 ≠ 3 then none else
  let destination ← yregOfNat (NaryaFormal.X86.bitField modrm 3 3)
  let source1 ← yregOfNat (15 - NaryaFormal.X86.bitField p1 3 4)
  let source2 ← yregOfNat (NaryaFormal.X86.bitField modrm 0 3)
  some (.shuffleI64x2 destination source1 source2 immediate, offset + 7)

def decodeBlock (bytes : List Nat) (offset : Nat) :
    Option (List Instruction) := do
  let (i0, o0) ← decodeUnpack bytes offset
  let (i1, o1) ← decodeUnpack bytes o0
  let (i2, o2) ← decodeUnpack bytes o1
  let (i3, o3) ← decodeUnpack bytes o2
  let (i4, o4) ← decodeShuffle bytes o3
  let (i5, o5) ← decodeShuffle bytes o4
  let (i6, o6) ← decodeShuffle bytes o5
  let (i7, _) ← decodeShuffle bytes o6
  some [i0, i1, i2, i3, i4, i5, i6, i7]

def expectedBlock : List Instruction := [
  .unpackLow 4 0 1,
  .unpackHigh 5 0 1,
  .unpackLow 6 2 3,
  .unpackHigh 7 2 3,
  .shuffleI64x2 0 4 6 0,
  .shuffleI64x2 1 5 7 0,
  .shuffleI64x2 2 4 6 3,
  .shuffleI64x2 3 5 7 3
]

def projectiveBlockOffsets : List Nat :=
  [52, 142, 237, 332, 427, 525, 623, 721, 831, 941]

def affineBlockOffsets : List Nat :=
  [67, 155, 260, 365, 470, 578, 686, 794, 890, 986]

theorem rejects_unpack_wrong_vector_length :
    decodeUnpack [0xc5, 0xf9, 0x6c, 0xe1] 0 = none := by
  decide

theorem rejects_shuffle_masked_form :
    decodeShuffle [0x62, 0xf3, 0xdd, 0x29, 0x43, 0xc6, 0] 0 = none := by
  decide

theorem changed_shuffle_immediate_changes_trace :
    decodeShuffle [0x62, 0xf3, 0xdd, 0x28, 0x43, 0xd6, 2] 0 =
      some (.shuffleI64x2 2 4 6 2, 7) := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem projective_assembled_shuffle_blocks_decode :
    ∀ offset ∈ projectiveBlockOffsets,
      decodeBlock NaryaFormal.TransposeObject.projectiveSymbolBytes offset =
        some expectedBlock := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem affine_assembled_shuffle_blocks_decode :
    ∀ offset ∈ affineBlockOffsets,
      decodeBlock NaryaFormal.TransposeObject.affineSymbolBytes offset =
        some expectedBlock := by
  decide

def RegisterState (α : Type u) := YReg → Q4 α

def initialState (input : Rows4 α) (scratch : Q4 α) : RegisterState α
  | 0 => input.r0
  | 1 => input.r1
  | 2 => input.r2
  | 3 => input.r3
  | _ => scratch

def executeInstruction (state : RegisterState α) :
    Instruction → RegisterState α
  | .unpackLow destination source1 source2 =>
      Function.update state destination (unpackLowQword (state source1) (state source2))
  | .unpackHigh destination source1 source2 =>
      Function.update state destination (unpackHighQword (state source1) (state source2))
  | .shuffleI64x2 destination source1 source2 immediate =>
      Function.update state destination
        (shuffleI64x2Ymm immediate (state source1) (state source2))

def runBlock (instructions : List Instruction) (state : RegisterState α) :
    RegisterState α :=
  instructions.foldl executeInstruction state

def outputRows (state : RegisterState α) : Rows4 α :=
  ⟨state 0, state 1, state 2, state 3⟩

/-- The exact register schedule decoded from every emitted block is the proved
mathematical 4x4 transpose, independent of all incoming scratch registers. -/
theorem expected_block_semantics (input : Rows4 α) (scratch : Q4 α) :
    outputRows (runBlock expectedBlock (initialState input scratch)) =
      transpose4Spec input := by
  have hbit31 : Nat.testBit 3 1 = true := by decide
  cases input with
  | mk r0 r1 r2 r3 =>
      cases r0
      cases r1
      cases r2
      cases r3
      cases scratch
      simp [runBlock, expectedBlock, executeInstruction, initialState,
        outputRows, Function.update, unpackLowQword, unpackHighQword,
        shuffleI64x2Ymm, transpose4Spec, hbit31]

end NaryaFormal.TransposeX86
