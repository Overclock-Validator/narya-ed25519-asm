#!/usr/bin/env python3
"""Generate the exact source-side whole-leaf transpose instruction traces.

The generator first validates the two assembly sources with a deliberately
narrow parser, then emits the semantic lists consumed by Lean.  It is not an
x86 decoder: the independent Lean decoder must decode the exact assembled
symbol bytes to these lists.
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

import check_transpose_object_trace as object_trace

ROOT = Path(__file__).resolve().parents[1]
PROJECTIVE_SOURCE = ROOT / "src/projective_niels_transpose_x8.S"
AFFINE_SOURCE = ROOT / "src/affine_niels_transpose_x8.S"
GENERATED = ROOT / "formal/lean/NaryaFormal/GeneratedTransposeWholeTrace.lean"

TRANSPOSE_MACRO = [
    "vpunpcklqdq ymm4, ymm0, ymm1",
    "vpunpckhqdq ymm5, ymm0, ymm1",
    "vpunpcklqdq ymm6, ymm2, ymm3",
    "vpunpckhqdq ymm7, ymm2, ymm3",
    "vshufi64x2 ymm0, ymm4, ymm6, 0x00",
    "vshufi64x2 ymm1, ymm5, ymm7, 0x00",
    "vshufi64x2 ymm2, ymm4, ymm6, 0x03",
    "vshufi64x2 ymm3, ymm5, ymm7, 0x03",
]

PROJECTIVE_HALF = [
    r"vmovdqu ymm0, YMMWORD PTR [\p0 + \off]",
    r"vmovdqu ymm1, YMMWORD PTR [\p1 + \off]",
    r"vmovdqu ymm2, YMMWORD PTR [\p2 + \off]",
    r"vmovdqu ymm3, YMMWORD PTR [\p3 + \off]",
    "TRANSPOSE_4X4",
    r"vmovdqu YMMWORD PTR [rax + 2*\off + \half], ymm0",
    r"vmovdqu YMMWORD PTR [rax + 320 + 2*\off + \half], ymm1",
    r"vmovdqu YMMWORD PTR [rax + 640 + 2*\off + \half], ymm2",
    r"vmovdqu YMMWORD PTR [rax + 960 + 2*\off + \half], ymm3",
]

AFFINE_HALF = [
    r"vmovdqu64 ymm0{k1}{z}, YMMWORD PTR [\p0 + \source_offset]",
    r"vmovdqu64 ymm1{k1}{z}, YMMWORD PTR [\p1 + \source_offset]",
    r"vmovdqu64 ymm2{k1}{z}, YMMWORD PTR [\p2 + \source_offset]",
    r"vmovdqu64 ymm3{k1}{z}, YMMWORD PTR [\p3 + \source_offset]",
    "TRANSPOSE_4X4",
    r"vmovdqu YMMWORD PTR [rax + \output_offset], ymm0",
    r"vmovdqu YMMWORD PTR [rax + 320 + \output_offset], ymm1",
    r"vmovdqu YMMWORD PTR [rax + 640 + \output_offset], ymm2",
]


def normalized_lines(text: str) -> list[str]:
    return [re.sub(r"\s+", " ", line.strip()) for line in text.splitlines() if line.strip()]


def macro_body(text: str, name: str) -> list[str]:
    match = re.search(
        rf"^\.macro {re.escape(name)}(?:[ \t]+[^\n]*)?\n(?P<body>.*?)^\.endm$",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise SystemExit(f"transpose trace extraction failed: missing macro {name}")
    return normalized_lines(match.group("body"))


def function_body(text: str, symbol: str) -> list[str]:
    clean = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    match = re.search(
        rf"^{re.escape(symbol)}:\n(?P<body>.*?)^\.size {re.escape(symbol)},",
        clean,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise SystemExit(f"transpose trace extraction failed: missing function {symbol}")
    return normalized_lines(match.group("body"))


def pointer_setup() -> list[str]:
    return [
        "mov rax, rdi",
        "mov rdx, QWORD PTR [rsi + 0]",
        "mov rcx, QWORD PTR [rsi + 8]",
        "mov r8, QWORD PTR [rsi + 16]",
        "mov r9, QWORD PTR [rsi + 24]",
        "mov r10, QWORD PTR [rsi + 32]",
        "mov r11, QWORD PTR [rsi + 40]",
        "mov rdi, QWORD PTR [rsi + 48]",
        "mov rsi, QWORD PTR [rsi + 56]",
    ]


def projective_calls() -> list[str]:
    result: list[str] = []
    for limb in range(5):
        offset = 32 * limb
        result.append(f"TRANSPOSE_HALF {offset}, 0, rdx, rcx, r8, r9")
        result.append(f"TRANSPOSE_HALF {offset}, 32, r10, r11, rdi, rsi")
    return result


def affine_calls() -> list[str]:
    result: list[str] = []
    for limb in range(5):
        source = 24 * limb
        output = 64 * limb
        result.append(f"TRANSPOSE_HALF {source}, {output}, rdx, rcx, r8, r9")
        result.append(f"TRANSPOSE_HALF {source}, {output + 32}, r10, r11, rdi, rsi")
    return result


def validate_source_texts(projective: str, affine: str) -> None:
    if macro_body(projective, "TRANSPOSE_4X4") != TRANSPOSE_MACRO:
        raise SystemExit("transpose trace extraction failed: projective shuffle macro changed")
    if macro_body(affine, "TRANSPOSE_4X4") != TRANSPOSE_MACRO:
        raise SystemExit("transpose trace extraction failed: affine shuffle macro changed")
    if macro_body(projective, "TRANSPOSE_HALF") != PROJECTIVE_HALF:
        raise SystemExit("transpose trace extraction failed: projective half macro changed")
    if macro_body(affine, "TRANSPOSE_HALF") != AFFINE_HALF:
        raise SystemExit("transpose trace extraction failed: affine half macro changed")
    projective_body = function_body(projective, object_trace.PROJECTIVE_SYMBOL)
    expected_projective = pointer_setup() + projective_calls() + ["vzeroupper", "ret"]
    if projective_body != expected_projective:
        raise SystemExit(
            "transpose trace extraction failed: projective pointer/call/epilogue trace changed\n"
            + "\n".join(difflib.unified_diff(expected_projective, projective_body))
        )
    affine_body = function_body(affine, object_trace.AFFINE_SYMBOL)
    expected_affine = ["mov eax, 7", "kmovb k1, eax"] + pointer_setup() + affine_calls() + [
        "vzeroupper",
        "ret",
    ]
    if affine_body != expected_affine:
        raise SystemExit(
            "transpose trace extraction failed: affine mask/pointer/call/epilogue trace changed\n"
            + "\n".join(difflib.unified_diff(expected_affine, affine_body))
        )


def validate_sources() -> None:
    validate_source_texts(
        PROJECTIVE_SOURCE.read_text(encoding="ascii"),
        AFFINE_SOURCE.read_text(encoding="ascii"),
    )


def zreg(value: int) -> str:
    return f"⟨{value}, by decide⟩"


def kreg(value: int) -> str:
    return f"⟨{value}, by decide⟩"


def gpr(value: object) -> str:
    return "." + str(value)


def lean_instruction(item: object_trace.Insn) -> str:
    op, args = item.op, item.args
    if op == "movReg64":
        return f".movReg64 {gpr(args[0])} {gpr(args[1])}"
    if op == "movLoad64":
        return f".movLoad64 {gpr(args[0])} {gpr(args[1])} {args[2]}"
    if op == "movImm32":
        return f".movImm32 {gpr(args[0])} {args[1]}"
    if op == "kmovb":
        return f".kmovb {kreg(int(args[0]))} {gpr(args[1])}"
    if op == "ymmLoad":
        return f".ymmLoad {zreg(int(args[0]))} {gpr(args[1])} {args[2]}"
    if op == "ymmMaskedLoad":
        zero = "true" if args[4] else "false"
        return (
            f".ymmMaskedLoad {zreg(int(args[0]))} {gpr(args[1])} {args[2]} "
            f"{kreg(int(args[3]))} {zero}"
        )
    if op == "ymmStore":
        return f".ymmStore {gpr(args[0])} {args[1]} {zreg(int(args[2]))}"
    if op == "unpackLow":
        return f".unpackLow {zreg(int(args[0]))} {zreg(int(args[1]))} {zreg(int(args[2]))}"
    if op == "unpackHigh":
        return f".unpackHigh {zreg(int(args[0]))} {zreg(int(args[1]))} {zreg(int(args[2]))}"
    if op == "shuffleI64x2":
        return (
            f".shuffleI64x2 {zreg(int(args[0]))} {zreg(int(args[1]))} "
            f"{zreg(int(args[2]))} {args[3]}"
        )
    if op == "vzeroUpper":
        return ".vzeroUpper"
    if op == "ret":
        return ".ret"
    raise SystemExit(f"unhandled semantic instruction {item}")


def render_list(name: str, program: tuple[object_trace.Insn, ...]) -> str:
    items = [lean_instruction(item) for item in program]
    lines = [f"def {name} : List Instruction := ["]
    lines.extend(f"  {item}," for item in items[:-1])
    lines.append(f"  {items[-1]}")
    lines.append("]")
    return "\n".join(lines)


def generate() -> str:
    validate_sources()
    projective = object_trace.expected_projective()
    affine = object_trace.expected_affine()
    return f'''/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

GENERATED FILE. DO NOT EDIT.
Generated from the exact pointer/mask/half-call schedules in the two transpose
assembly sources by tools/generate_transpose_whole_trace.py.  This is the
source-side semantic transcript, not an x86 decoder.
-/

import NaryaFormal.TransposeX86WholeInstruction

namespace NaryaFormal.TransposeWholeX86.Generated

{render_list("projectiveProgram", projective)}

{render_list("affineProgram", affine)}

def projectiveBody : List Instruction := projectiveProgram.take {len(projective) - 2}
def affineBody : List Instruction := affineProgram.take {len(affine) - 2}
def epilogue : List Instruction := [.vzeroUpper, .ret]

set_option maxRecDepth 4096 in
theorem projective_program_split :
    projectiveProgram = projectiveBody ++ epilogue := by
  decide

set_option maxRecDepth 4096 in
theorem affine_program_split :
    affineProgram = affineBody ++ epilogue := by
  decide

set_option maxRecDepth 4096 in
theorem projective_instruction_count : projectiveProgram.length = {len(projective)} := by
  decide

set_option maxRecDepth 4096 in
theorem affine_instruction_count : affineProgram.length = {len(affine)} := by
  decide

end NaryaFormal.TransposeWholeX86.Generated
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = generate()
    if args.output:
        args.output.write_text(generated, encoding="utf-8")
    elif args.check:
        committed = GENERATED.read_text(encoding="utf-8")
        if committed != generated:
            sys.stderr.writelines(
                difflib.unified_diff(
                    committed.splitlines(keepends=True),
                    generated.splitlines(keepends=True),
                    fromfile=str(GENERATED.relative_to(ROOT)),
                    tofile="generated transpose whole-leaf trace",
                )
            )
            raise SystemExit(1)
        print("OK: transpose source whole-leaf traces match committed Lean input")
    else:
        print(generated, end="")


if __name__ == "__main__":
    main()
