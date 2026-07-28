/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

GENERATED FILE. DO NOT EDIT.
Generated from src/r51x8_ifma.S by
tools/generate_r51_instruction_trace.py.
This is the source-side instruction trace, not an x86 decoder.
-/

import NaryaFormal.X86Decoder

namespace NaryaFormal.X86.GeneratedR51InstructionTrace

def loadPhase : List Instruction := [
  .vmovdqu64Load ⟨0, by decide⟩ .rsi 0,
  .vmovdqu64Load ⟨1, by decide⟩ .rsi 64,
  .vmovdqu64Load ⟨2, by decide⟩ .rsi 128,
  .vmovdqu64Load ⟨3, by decide⟩ .rsi 192,
  .vmovdqu64Load ⟨4, by decide⟩ .rsi 256,
  .vmovdqu64Load ⟨5, by decide⟩ .rdx 0,
  .vmovdqu64Load ⟨6, by decide⟩ .rdx 64,
  .vmovdqu64Load ⟨7, by decide⟩ .rdx 128,
  .vmovdqu64Load ⟨8, by decide⟩ .rdx 192,
  .vmovdqu64Load ⟨9, by decide⟩ .rdx 256
]

def clearPhase : List Instruction := [
  .vpxorq ⟨10, by decide⟩ ⟨10, by decide⟩ ⟨10, by decide⟩,
  .vpxorq ⟨11, by decide⟩ ⟨11, by decide⟩ ⟨11, by decide⟩,
  .vpxorq ⟨12, by decide⟩ ⟨12, by decide⟩ ⟨12, by decide⟩,
  .vpxorq ⟨13, by decide⟩ ⟨13, by decide⟩ ⟨13, by decide⟩,
  .vpxorq ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨14, by decide⟩,
  .vpxorq ⟨15, by decide⟩ ⟨15, by decide⟩ ⟨15, by decide⟩,
  .vpxorq ⟨16, by decide⟩ ⟨16, by decide⟩ ⟨16, by decide⟩,
  .vpxorq ⟨17, by decide⟩ ⟨17, by decide⟩ ⟨17, by decide⟩,
  .vpxorq ⟨18, by decide⟩ ⟨18, by decide⟩ ⟨18, by decide⟩,
  .vpxorq ⟨19, by decide⟩ ⟨19, by decide⟩ ⟨19, by decide⟩,
  .vpxorq ⟨20, by decide⟩ ⟨20, by decide⟩ ⟨20, by decide⟩,
  .vpxorq ⟨21, by decide⟩ ⟨21, by decide⟩ ⟨21, by decide⟩,
  .vpxorq ⟨22, by decide⟩ ⟨22, by decide⟩ ⟨22, by decide⟩,
  .vpxorq ⟨23, by decide⟩ ⟨23, by decide⟩ ⟨23, by decide⟩,
  .vpxorq ⟨24, by decide⟩ ⟨24, by decide⟩ ⟨24, by decide⟩,
  .vpxorq ⟨25, by decide⟩ ⟨25, by decide⟩ ⟨25, by decide⟩,
  .vpxorq ⟨26, by decide⟩ ⟨26, by decide⟩ ⟨26, by decide⟩,
  .vpxorq ⟨27, by decide⟩ ⟨27, by decide⟩ ⟨27, by decide⟩
]

def productPhase : List Instruction := [
  .vpmadd52luq ⟨10, by decide⟩ ⟨0, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52huq ⟨19, by decide⟩ ⟨0, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52luq ⟨11, by decide⟩ ⟨0, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52huq ⟨20, by decide⟩ ⟨0, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52luq ⟨12, by decide⟩ ⟨0, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52huq ⟨21, by decide⟩ ⟨0, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52luq ⟨13, by decide⟩ ⟨0, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52huq ⟨22, by decide⟩ ⟨0, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52luq ⟨14, by decide⟩ ⟨0, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52huq ⟨23, by decide⟩ ⟨0, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52luq ⟨11, by decide⟩ ⟨1, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52huq ⟨20, by decide⟩ ⟨1, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52luq ⟨12, by decide⟩ ⟨1, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52huq ⟨21, by decide⟩ ⟨1, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52luq ⟨13, by decide⟩ ⟨1, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52huq ⟨22, by decide⟩ ⟨1, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52luq ⟨14, by decide⟩ ⟨1, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52huq ⟨23, by decide⟩ ⟨1, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52luq ⟨15, by decide⟩ ⟨1, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52huq ⟨24, by decide⟩ ⟨1, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52luq ⟨12, by decide⟩ ⟨2, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52huq ⟨21, by decide⟩ ⟨2, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52luq ⟨13, by decide⟩ ⟨2, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52huq ⟨22, by decide⟩ ⟨2, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52luq ⟨14, by decide⟩ ⟨2, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52huq ⟨23, by decide⟩ ⟨2, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52luq ⟨15, by decide⟩ ⟨2, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52huq ⟨24, by decide⟩ ⟨2, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52luq ⟨16, by decide⟩ ⟨2, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52huq ⟨25, by decide⟩ ⟨2, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52luq ⟨13, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52huq ⟨22, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52luq ⟨14, by decide⟩ ⟨3, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52huq ⟨23, by decide⟩ ⟨3, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52luq ⟨15, by decide⟩ ⟨3, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52huq ⟨24, by decide⟩ ⟨3, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52luq ⟨16, by decide⟩ ⟨3, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52huq ⟨25, by decide⟩ ⟨3, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52luq ⟨17, by decide⟩ ⟨3, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52huq ⟨26, by decide⟩ ⟨3, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52luq ⟨14, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52huq ⟨23, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩,
  .vpmadd52luq ⟨15, by decide⟩ ⟨4, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52huq ⟨24, by decide⟩ ⟨4, by decide⟩ ⟨6, by decide⟩,
  .vpmadd52luq ⟨16, by decide⟩ ⟨4, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52huq ⟨25, by decide⟩ ⟨4, by decide⟩ ⟨7, by decide⟩,
  .vpmadd52luq ⟨17, by decide⟩ ⟨4, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52huq ⟨26, by decide⟩ ⟨4, by decide⟩ ⟨8, by decide⟩,
  .vpmadd52luq ⟨18, by decide⟩ ⟨4, by decide⟩ ⟨9, by decide⟩,
  .vpmadd52huq ⟨27, by decide⟩ ⟨4, by decide⟩ ⟨9, by decide⟩
]

def combinePhase : List Instruction := [
  .vpsllq ⟨19, by decide⟩ ⟨19, by decide⟩ 1,
  .vpaddq ⟨11, by decide⟩ ⟨11, by decide⟩ ⟨19, by decide⟩,
  .vpsllq ⟨20, by decide⟩ ⟨20, by decide⟩ 1,
  .vpaddq ⟨12, by decide⟩ ⟨12, by decide⟩ ⟨20, by decide⟩,
  .vpsllq ⟨21, by decide⟩ ⟨21, by decide⟩ 1,
  .vpaddq ⟨13, by decide⟩ ⟨13, by decide⟩ ⟨21, by decide⟩,
  .vpsllq ⟨22, by decide⟩ ⟨22, by decide⟩ 1,
  .vpaddq ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩,
  .vpsllq ⟨23, by decide⟩ ⟨23, by decide⟩ 1,
  .vpaddq ⟨15, by decide⟩ ⟨15, by decide⟩ ⟨23, by decide⟩,
  .vpsllq ⟨24, by decide⟩ ⟨24, by decide⟩ 1,
  .vpaddq ⟨16, by decide⟩ ⟨16, by decide⟩ ⟨24, by decide⟩,
  .vpsllq ⟨25, by decide⟩ ⟨25, by decide⟩ 1,
  .vpaddq ⟨17, by decide⟩ ⟨17, by decide⟩ ⟨25, by decide⟩,
  .vpsllq ⟨26, by decide⟩ ⟨26, by decide⟩ 1,
  .vpaddq ⟨18, by decide⟩ ⟨18, by decide⟩ ⟨26, by decide⟩,
  .vpsllq ⟨27, by decide⟩ ⟨27, by decide⟩ 1
]

def foldPhase : List Instruction := [
  .vpbroadcastq ⟨30, by decide⟩ R51Object.ifma_fold19Address,
  .vpmullq ⟨28, by decide⟩ ⟨15, by decide⟩ ⟨30, by decide⟩,
  .vpaddq ⟨10, by decide⟩ ⟨10, by decide⟩ ⟨28, by decide⟩,
  .vpmullq ⟨28, by decide⟩ ⟨16, by decide⟩ ⟨30, by decide⟩,
  .vpaddq ⟨11, by decide⟩ ⟨11, by decide⟩ ⟨28, by decide⟩,
  .vpmullq ⟨28, by decide⟩ ⟨17, by decide⟩ ⟨30, by decide⟩,
  .vpaddq ⟨12, by decide⟩ ⟨12, by decide⟩ ⟨28, by decide⟩,
  .vpmullq ⟨28, by decide⟩ ⟨18, by decide⟩ ⟨30, by decide⟩,
  .vpaddq ⟨13, by decide⟩ ⟨13, by decide⟩ ⟨28, by decide⟩,
  .vpmullq ⟨28, by decide⟩ ⟨27, by decide⟩ ⟨30, by decide⟩,
  .vpaddq ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨28, by decide⟩
]

def normalizePhase : List Instruction := [
  .vpbroadcastq ⟨5, by decide⟩ R51Object.ifma_mask51Address,
  .vpsrlq ⟨15, by decide⟩ ⟨10, by decide⟩ 51,
  .vpsrlq ⟨16, by decide⟩ ⟨11, by decide⟩ 51,
  .vpsrlq ⟨17, by decide⟩ ⟨12, by decide⟩ 51,
  .vpsrlq ⟨18, by decide⟩ ⟨13, by decide⟩ 51,
  .vpsrlq ⟨19, by decide⟩ ⟨14, by decide⟩ 51,
  .vpandq ⟨10, by decide⟩ ⟨10, by decide⟩ ⟨5, by decide⟩,
  .vpandq ⟨11, by decide⟩ ⟨11, by decide⟩ ⟨5, by decide⟩,
  .vpandq ⟨12, by decide⟩ ⟨12, by decide⟩ ⟨5, by decide⟩,
  .vpandq ⟨13, by decide⟩ ⟨13, by decide⟩ ⟨5, by decide⟩,
  .vpandq ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨5, by decide⟩,
  .vpaddq ⟨11, by decide⟩ ⟨11, by decide⟩ ⟨15, by decide⟩,
  .vpaddq ⟨12, by decide⟩ ⟨12, by decide⟩ ⟨16, by decide⟩,
  .vpaddq ⟨13, by decide⟩ ⟨13, by decide⟩ ⟨17, by decide⟩,
  .vpaddq ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨18, by decide⟩,
  .vpmadd52luq ⟨10, by decide⟩ ⟨30, by decide⟩ ⟨19, by decide⟩
]

def storePhase : List Instruction := [
  .vmovdqu64Store .rdi 0 ⟨10, by decide⟩,
  .vmovdqu64Store .rdi 64 ⟨11, by decide⟩,
  .vmovdqu64Store .rdi 128 ⟨12, by decide⟩,
  .vmovdqu64Store .rdi 192 ⟨13, by decide⟩,
  .vmovdqu64Store .rdi 256 ⟨14, by decide⟩
]

def epiloguePhase : List Instruction := [
  .vzeroUpper,
  .ret
]

def expectedProgram : List Instruction :=
  loadPhase ++ clearPhase ++ productPhase ++ combinePhase ++
  foldPhase ++ normalizePhase ++ storePhase ++ epiloguePhase

set_option maxRecDepth 4096 in
theorem phase_lengths :
    loadPhase.length = 10 ∧ clearPhase.length = 18 ∧
    productPhase.length = 50 ∧ combinePhase.length = 17 ∧
    foldPhase.length = 11 ∧ normalizePhase.length = 16 ∧
    storePhase.length = 5 ∧ epiloguePhase.length = 2 := by
  decide

set_option maxRecDepth 4096 in
theorem expected_instruction_count : expectedProgram.length = 129 := by
  decide

end NaryaFormal.X86.GeneratedR51InstructionTrace
