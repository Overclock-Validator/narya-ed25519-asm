/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Fail-closed decoder for the exact x86-64 instruction forms used by
narya_r51x8_mul_ifma. This is intentionally not a general x86 decoder. Every
EVEX field that is fixed by the supported form is checked, and unsupported
opcodes, masks, vector lengths, addressing modes, and negative compressed
displacements are rejected.
-/

import NaryaFormal.GeneratedR51ObjectBytes
import NaryaFormal.X86Machine

namespace NaryaFormal.X86

inductive Instruction
  | vmovdqu64Load (destination : ZReg) (base : Gpr) (displacement : Nat)
  | vmovdqu64Store (base : Gpr) (displacement : Nat) (source : ZReg)
  | vpxorq (destination source1 source2 : ZReg)
  | vpmadd52luq (destination source1 source2 : ZReg)
  | vpmadd52huq (destination source1 source2 : ZReg)
  | vpaddq (destination source1 source2 : ZReg)
  | vpmullq (destination source1 source2 : ZReg)
  | vpandq (destination source1 source2 : ZReg)
  | vpsllq (destination source : ZReg) (amount : Nat)
  | vpsrlq (destination source : ZReg) (amount : Nat)
  | vpbroadcastq (destination : ZReg) (absoluteAddress : Nat)
  | vzeroUpper
  | ret
  deriving DecidableEq, Repr

structure EvexHeader where
  p0 : Nat
  p1 : Nat
  p2 : Nat
  opcode : Nat
  modrm : Nat
  deriving DecidableEq, Repr

def byteAt (bytes : List Nat) (offset : Nat) : Option Nat :=
  match bytes[offset]? with
  | some value => if value < 256 then some value else none
  | none => none

def bitField (value start width : Nat) : Nat :=
  value / 2 ^ start % 2 ^ width

def bit (value index : Nat) : Nat := bitField value index 1

def invertedBit (value : Nat) : Nat := 1 - value

def zregOfNat (value : Nat) : Option ZReg :=
  if hvalue : value < 32 then some ⟨value, hvalue⟩ else none

def readEvexHeader (bytes : List Nat) (offset : Nat) : Option EvexHeader := do
  let marker ← byteAt bytes offset
  if marker ≠ 0x62 then none else
  let p0 ← byteAt bytes (offset + 1)
  let p1 ← byteAt bytes (offset + 2)
  let p2 ← byteAt bytes (offset + 3)
  let opcode ← byteAt bytes (offset + 4)
  let modrm ← byteAt bytes (offset + 5)
  some { p0, p1, p2, opcode, modrm }

/-- Common qword-ZMM constraints: selected opcode map, W=1, required prefix,
    EVEX fixed bit=1, no masking/zeroing/broadcast, and 512-bit vector length.
    P2 differs only in the inverted fifth vvvv bit. -/
def validEvexQwordZmm (header : EvexHeader)
    (opcodeMap mandatoryPrefix : Nat) : Bool :=
  decide (
    header.p0 % 8 = opcodeMap ∧ bit header.p0 3 = 0 ∧
    bit header.p1 7 = 1 ∧ header.p1 % 8 = 4 + mandatoryPrefix ∧
    (header.p2 = 0x48 ∨ header.p2 = 0x40))

def evexDestination (header : EvexHeader) : Option ZReg :=
  zregOfNat
    (bitField header.modrm 3 3 +
      8 * invertedBit (bit header.p0 7) +
      16 * invertedBit (bit header.p0 4))

def evexSource1 (header : EvexHeader) : Option ZReg :=
  zregOfNat
    ((15 - bitField header.p1 3 4) +
      16 * invertedBit (bit header.p2 3))

def evexRmRegister (header : EvexHeader) : Option ZReg :=
  zregOfNat
    (bitField header.modrm 0 3 +
      8 * invertedBit (bit header.p0 5) +
      16 * invertedBit (bit header.p0 6))

def modrmMode (header : EvexHeader) : Nat := bitField header.modrm 6 2
def modrmReg (header : EvexHeader) : Nat := bitField header.modrm 3 3
def modrmRm (header : EvexHeader) : Nat := bitField header.modrm 0 3

def reservedVvvv (header : EvexHeader) : Bool :=
  decide (bitField header.p1 3 4 = 15 ∧ bit header.p2 3 = 1)

def memoryBaseUnextended (header : EvexHeader) : Bool :=
  decide (bit header.p0 5 = 1 ∧ bit header.p0 6 = 1)

def groupRegUnextended (header : EvexHeader) : Bool :=
  decide (bit header.p0 7 = 1 ∧ bit header.p0 4 = 1)

def gprBaseOfRm (value : Nat) : Option Gpr :=
  match value with
  | 2 => some .rdx
  | 6 => some .rsi
  | 7 => some .rdi
  | _ => none

def decodeVmovdqu64 (bytes : List Nat) (offset : Nat)
    (header : EvexHeader) : Option (Instruction × Nat) := do
  if !validEvexQwordZmm header 1 2 || !reservedVvvv header ||
      !memoryBaseUnextended header then none else
  let vector ← evexDestination header
  let base ← gprBaseOfRm (modrmRm header)
  let (displacement, nextOffset) ←
    match modrmMode header with
    | 0 => some (0, offset + 6)
    | 1 => do
        let compressed ← byteAt bytes (offset + 6)
        -- The proof leaf uses only nonnegative EVEX full-vector disp8 values.
        if compressed < 128 then some (64 * compressed, offset + 7) else none
    | _ => none
  match header.opcode with
  | 0x6f => some (.vmovdqu64Load vector base displacement, nextOffset)
  | 0x7f => some (.vmovdqu64Store base displacement vector, nextOffset)
  | _ => none

def decodeTernaryRegister (header : EvexHeader) : Option (Instruction × Nat) := do
  if !validEvexQwordZmm header (header.p0 % 8) 1 ||
      modrmMode header ≠ 3 then none else
  let destination ← evexDestination header
  let source1 ← evexSource1 header
  let source2 ← evexRmRegister header
  let instruction ←
    match header.p0 % 8, header.opcode with
    | 1, 0xef => some (.vpxorq destination source1 source2)
    | 1, 0xd4 => some (.vpaddq destination source1 source2)
    | 1, 0xdb => some (.vpandq destination source1 source2)
    | 2, 0xb4 => some (.vpmadd52luq destination source1 source2)
    | 2, 0xb5 => some (.vpmadd52huq destination source1 source2)
    | 2, 0x40 => some (.vpmullq destination source1 source2)
    | _, _ => none
  some (instruction, 6)

def decodeShift (bytes : List Nat) (offset : Nat)
    (header : EvexHeader) : Option (Instruction × Nat) := do
  if header.opcode ≠ 0x73 || !validEvexQwordZmm header 1 1 ||
      modrmMode header ≠ 3 || !groupRegUnextended header then none else
  let destination ← evexSource1 header
  let source ← evexRmRegister header
  let amount ← byteAt bytes (offset + 6)
  if 64 ≤ amount then none else
  let instruction ←
    match modrmReg header with
    | 6 => some (.vpsllq destination source amount)
    | 2 => some (.vpsrlq destination source amount)
    | _ => none
  some (instruction, offset + 7)

def littleEndian32 (bytes : List Nat) (offset : Nat) : Option Nat := do
  let b0 ← byteAt bytes offset
  let b1 ← byteAt bytes (offset + 1)
  let b2 ← byteAt bytes (offset + 2)
  let b3 ← byteAt bytes (offset + 3)
  some (b0 + 256 * b1 + 256 ^ 2 * b2 + 256 ^ 3 * b3)

def decodeBroadcast (baseAddress : Nat) (bytes : List Nat) (offset : Nat)
    (header : EvexHeader) : Option (Instruction × Nat) := do
  if header.opcode ≠ 0x59 || !validEvexQwordZmm header 2 1 ||
      modrmMode header ≠ 0 || modrmRm header ≠ 5 ||
      !reservedVvvv header || !memoryBaseUnextended header then none else
  let destination ← evexDestination header
  let displacement ← littleEndian32 bytes (offset + 6)
  -- The proof ELF places both constants after the leaf, so only a positive
  -- signed disp32 form is admitted by this specialized decoder.
  if 2 ^ 31 ≤ displacement then none else
  let absoluteAddress := baseAddress + offset + 10 + displacement
  if 2 ^ 64 ≤ absoluteAddress then none else
  some (.vpbroadcastq destination absoluteAddress, offset + 10)

def decodeEvex (baseAddress : Nat) (bytes : List Nat) (offset : Nat)
    (header : EvexHeader) : Option (Instruction × Nat) :=
  if header.opcode = 0x6f ∨ header.opcode = 0x7f then
    decodeVmovdqu64 bytes offset header
  else if header.opcode = 0x73 then
    decodeShift bytes offset header
  else if header.opcode = 0x59 then
    decodeBroadcast baseAddress bytes offset header
  else do
    let (instruction, length) ← decodeTernaryRegister header
    some (instruction, offset + length)

def decodeOne (baseAddress : Nat) (bytes : List Nat) (offset : Nat) :
    Option (Instruction × Nat) := do
  let first ← byteAt bytes offset
  if first = 0xc3 then
    some (.ret, offset + 1)
  else if first = 0xc5 then
    let second ← byteAt bytes (offset + 1)
    let third ← byteAt bytes (offset + 2)
    if second = 0xf8 ∧ third = 0x77 then
      some (.vzeroUpper, offset + 3)
    else none
  else if first = 0x62 then
    let header ← readEvexHeader bytes offset
    decodeEvex baseAddress bytes offset header
  else none

def decodeProgramAux (baseAddress : Nat) (bytes : List Nat) :
    Nat → Nat → Option (List Instruction)
  | 0, _ => none
  | fuel + 1, offset => do
      let (instruction, nextOffset) ← decodeOne baseAddress bytes offset
      if nextOffset ≤ offset then none else
      if instruction = .ret then
        if nextOffset = bytes.length then some [.ret] else none
      else
        let rest ← decodeProgramAux baseAddress bytes fuel nextOffset
        some (instruction :: rest)

def decodeProgram (baseAddress : Nat) (bytes : List Nat) :
    Option (List Instruction) :=
  decodeProgramAux baseAddress bytes (bytes.length + 1) 0

def decodedR51Program : List Instruction :=
  (decodeProgram R51Object.symbolAddress R51Object.symbolBytes).getD []

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem r51_symbol_decode_succeeds :
    decodeProgram R51Object.symbolAddress R51Object.symbolBytes =
      some decodedR51Program := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem r51_decoded_instruction_count : decodedR51Program.length = 129 := by
  decide

theorem rejects_masked_vmov :
    decodeOne 0 [0x62, 0xf1, 0xfe, 0x49, 0x6f, 0x06] 0 = none := by
  decide

theorem rejects_wrong_vector_length :
    decodeOne 0 [0x62, 0xf1, 0xfe, 0x28, 0x6f, 0x06] 0 = none := by
  decide

theorem rejects_negative_compressed_displacement :
    decodeOne 0 [0x62, 0xf1, 0xfe, 0x48, 0x6f, 0x4e, 0xff] 0 = none := by
  decide

theorem rejects_unsupported_opcode :
    decodeOne 0 [0x62, 0xf1, 0xfd, 0x48, 0x58, 0xc0] 0 = none := by
  decide

end NaryaFormal.X86
