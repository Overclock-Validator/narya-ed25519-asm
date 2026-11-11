/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Fail-closed decoder for the exact GPR, mask, YMM memory, shuffle, store, and
epilogue instruction forms used by the two Niels transpose symbols.  It is not
a general x86 decoder.
-/

import NaryaFormal.GeneratedTransposeObjectBytes
import NaryaFormal.GeneratedTransposeWholeTrace

namespace NaryaFormal.TransposeWholeX86

open NaryaFormal.X86


def gprOfEncoding : Nat → Option Gpr
  | 0 => some .rax
  | 1 => some .rcx
  | 2 => some .rdx
  | 3 => some .rbx
  | 4 => some .rsp
  | 5 => some .rbp
  | 6 => some .rsi
  | 7 => some .rdi
  | 8 => some .r8
  | 9 => some .r9
  | 10 => some .r10
  | 11 => some .r11
  | 12 => some .r12
  | 13 => some .r13
  | 14 => some .r14
  | 15 => some .r15
  | _ => none


def zregOfEncoding (value : Nat) : Option ZReg :=
  if hvalue : value < 32 then some ⟨value, hvalue⟩ else none


def kregOfEncoding (value : Nat) : Option KReg :=
  if hvalue : value < 8 then some ⟨value, hvalue⟩ else none


def signedDisp8 (value : Nat) : Option Nat :=
  if value < 128 then some value else none


def positiveDisp32 (bytes : List Nat) (offset : Nat) : Option Nat := do
  let value ← littleEndian32 bytes offset
  if value < 2 ^ 31 then some value else none


def decodeMemoryAddress (bytes : List Nat) (offset mode rm baseExtension scale : Nat) :
    Option (Gpr × Nat × Nat) := do
  if rm = 4 then none else
  if mode = 0 ∧ rm = 5 then none else
  let base ← gprOfEncoding (rm + 8 * baseExtension)
  match mode with
  | 0 => some (base, 0, offset)
  | 1 => do
      let compressed ← byteAt bytes offset
      let displacement ← signedDisp8 compressed
      some (base, displacement * scale, offset + 1)
  | 2 => do
      let displacement ← positiveDisp32 bytes offset
      some (base, displacement, offset + 4)
  | _ => none


def decodeRex (bytes : List Nat) (offset rex : Nat) : Option (Instruction × Nat) := do
  let opcode ← byteAt bytes (offset + 1)
  let modrm ← byteAt bytes (offset + 2)
  let mode := bitField modrm 6 2
  let regEncoding := bitField modrm 3 3 + 8 * bit rex 2
  let rmEncoding := bitField modrm 0 3 + 8 * bit rex 0
  if opcode = 0x89 ∧ mode = 3 then do
    let destination ← gprOfEncoding rmEncoding
    let source ← gprOfEncoding regEncoding
    some (.movReg64 destination source, offset + 3)
  else if opcode = 0x8b ∧ mode ≠ 3 then do
    let destination ← gprOfEncoding regEncoding
    let (base, displacement, nextOffset) ←
      decodeMemoryAddress bytes (offset + 3) mode (bitField modrm 0 3) (bit rex 0) 1
    some (.movLoad64 destination base displacement, nextOffset)
  else none


def decodeVex2 (bytes : List Nat) (offset : Nat) : Option (Instruction × Nat) := do
  let p1 ← byteAt bytes (offset + 1)
  let opcode ← byteAt bytes (offset + 2)
  if p1 = 0xf8 ∧ opcode = 0x77 then
    some (.vzeroUpper, offset + 3)
  else do
    let modrm ← byteAt bytes (offset + 3)
    let mode := bitField modrm 6 2
    if opcode = 0x92 then do
      if p1 ≠ 0xf9 ∨ mode ≠ 3 then none else
      let destination ← kregOfEncoding (bitField modrm 3 3)
      let source ← gprOfEncoding (bitField modrm 0 3)
      some (.kmovb destination source, offset + 4)
    else do
      if bit p1 2 ≠ 1 then none else
      let destination ← zregOfEncoding
        (bitField modrm 3 3 + 8 * invertedBit (bit p1 7))
      let source1 ← zregOfEncoding (15 - bitField p1 3 4)
      if (opcode = 0x6c ∨ opcode = 0x6d) then do
        if p1 % 4 ≠ 1 ∨ mode ≠ 3 then none else
        let source2 ← zregOfEncoding (bitField modrm 0 3)
        let instruction := if opcode = 0x6c then
          .unpackLow destination source1 source2
        else
          .unpackHigh destination source1 source2
        some (instruction, offset + 4)
      else if opcode = 0x6f ∨ opcode = 0x7f then do
        if p1 % 4 ≠ 2 ∨ bitField p1 3 4 ≠ 15 ∨ mode = 3 then none else
        let (base, displacement, nextOffset) ←
          decodeMemoryAddress bytes (offset + 4) mode (bitField modrm 0 3) 0 1
        if opcode = 0x6f then
          some (.ymmLoad destination base displacement, nextOffset)
        else
          some (.ymmStore base displacement destination, nextOffset)
      else none


def decodeVex3 (bytes : List Nat) (offset : Nat) : Option (Instruction × Nat) := do
  let p0 ← byteAt bytes (offset + 1)
  let p1 ← byteAt bytes (offset + 2)
  let opcode ← byteAt bytes (offset + 3)
  let modrm ← byteAt bytes (offset + 4)
  let mode := bitField modrm 6 2
  if p0 % 32 ≠ 1 ∨ bit p0 6 ≠ 1 ∨ bit p1 7 ≠ 0 ∨
      bitField p1 3 4 ≠ 15 ∨ bit p1 2 ≠ 1 ∨ p1 % 4 ≠ 2 ∨
      opcode ≠ 0x6f ∨ mode = 3 then none else
  let destination ← zregOfEncoding
    (bitField modrm 3 3 + 8 * invertedBit (bit p0 7))
  let (base, displacement, nextOffset) ←
    decodeMemoryAddress bytes (offset + 5) mode (bitField modrm 0 3)
      (invertedBit (bit p0 5)) 1
  some (.ymmLoad destination base displacement, nextOffset)


def decodeEvex (bytes : List Nat) (offset : Nat) : Option (Instruction × Nat) := do
  let p0 ← byteAt bytes (offset + 1)
  let p1 ← byteAt bytes (offset + 2)
  let p2 ← byteAt bytes (offset + 3)
  let opcode ← byteAt bytes (offset + 4)
  let modrm ← byteAt bytes (offset + 5)
  let mode := bitField modrm 6 2
  let destination ← zregOfEncoding
    (bitField modrm 3 3 + 8 * invertedBit (bit p0 7) +
      16 * invertedBit (bit p0 4))
  if opcode = 0x43 then do
    if p0 % 8 ≠ 3 ∨ bit p0 3 ≠ 0 ∨ bit p1 7 ≠ 1 ∨
        p1 % 8 ≠ 5 ∨ p2 ≠ 0x28 ∨ mode ≠ 3 then
      none
    else
      let source1 ← zregOfEncoding
        ((15 - bitField p1 3 4) + 16 * invertedBit (bit p2 3))
      let source2 ← zregOfEncoding
        (bitField modrm 0 3 + 8 * invertedBit (bit p0 6) +
          16 * invertedBit (bit p0 5))
      let immediate ← byteAt bytes (offset + 6)
      some (.shuffleI64x2 destination source1 source2 immediate, offset + 7)
  else if opcode = 0x6f then do
    if p0 % 8 ≠ 1 ∨ bit p0 3 ≠ 0 ∨ bit p0 6 ≠ 1 ∨
        bit p1 7 ≠ 1 ∨ p1 % 8 ≠ 6 ∨
        bitField p1 3 4 ≠ 15 ∨ bit p2 3 ≠ 1 ∨ bitField p2 5 2 ≠ 1 ∨
        bit p2 4 ≠ 0 ∨ mode = 3 then none else
    let mask ← kregOfEncoding (bitField p2 0 3)
    let zeroing := bit p2 7 = 1
    let (base, displacement, nextOffset) ←
      decodeMemoryAddress bytes (offset + 6) mode (bitField modrm 0 3)
        (invertedBit (bit p0 5)) 32
    some (.ymmMaskedLoad destination base displacement mask zeroing, nextOffset)
  else none


def decodeOne (bytes : List Nat) (offset : Nat) : Option (Instruction × Nat) := do
  let first ← byteAt bytes offset
  if first = 0xc3 then
    some (.ret, offset + 1)
  else if first = 0xb8 then do
    let immediate ← littleEndian32 bytes (offset + 1)
    some (.movImm32 .rax immediate, offset + 5)
  else if first = 0x48 ∨ first = 0x4c then
    decodeRex bytes offset first
  else if first = 0xc5 then
    decodeVex2 bytes offset
  else if first = 0xc4 then
    decodeVex3 bytes offset
  else if first = 0x62 then
    decodeEvex bytes offset
  else none


def decodeProgramAux (bytes : List Nat) : Nat → Nat → Option (List Instruction)
  | 0, _ => none
  | fuel + 1, offset => do
      let (instruction, nextOffset) ← decodeOne bytes offset
      if nextOffset ≤ offset then none else
      if instruction = .ret then
        if nextOffset = bytes.length then some [.ret] else none
      else
        let rest ← decodeProgramAux bytes fuel nextOffset
        some (instruction :: rest)


def decodeProgram (bytes : List Nat) : Option (List Instruction) :=
  decodeProgramAux bytes (bytes.length + 1) 0


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem projective_whole_symbol_decodes :
    decodeProgram NaryaFormal.TransposeObject.projectiveSymbolBytes =
      some Generated.projectiveProgram := by
  decide


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem affine_whole_symbol_decodes :
    decodeProgram NaryaFormal.TransposeObject.affineSymbolBytes =
      some Generated.affineProgram := by
  decide


theorem changed_affine_mask_fields_change_trace :
    decodeOne [0x62, 0xf1, 0xfe, 0x28, 0x6f, 0x02] 0 =
      some (.ymmMaskedLoad 0 .rdx 0 0 false, 6) := by
  decide


theorem rejects_affine_wrong_vector_length :
    decodeOne [0x62, 0xf1, 0xfe, 0xc9, 0x6f, 0x02] 0 = none := by
  decide

end NaryaFormal.TransposeWholeX86
