#!/usr/bin/env python3
"""Certify the lane map of Narya's two x8 transpose assembly leaves.

This checker deliberately has a narrow instruction vocabulary. It parses and
symbolically executes the actual TRANSPOSE_4X4 macro, then validates the exact
load/store templates, source-pointer map, and ten limb/half invocations in each
assembly file. An unsupported instruction or layout change fails closed.

The instruction semantics are the EVEX.256 cases from Intel SDM Vol. 2C:
VSHUFI64X2 selects the first source's 128-bit half with imm8[0] and the
second source's 128-bit half with imm8[1]. VPUNPCKL/HQDQ operate independently
in both 128-bit halves.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def normalized_lines(text: str) -> list[str]:
    return [re.sub(r"\s+", " ", line.strip()) for line in text.splitlines() if line.strip()]


def macro_body(text: str, name: str) -> list[str]:
    match = re.search(
        rf"^\.macro {re.escape(name)}(?:[ \t]+[^\n]*)?\n(?P<body>.*?)^\.endm$",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise AssertionError(f"missing macro {name}")
    return normalized_lines(match.group("body"))


def function_body(text: str, symbol: str) -> list[str]:
    match = re.search(
        rf"^{re.escape(symbol)}:\n(?P<body>.*?)^\.size {re.escape(symbol)},",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise AssertionError(f"missing function {symbol}")
    return normalized_lines(match.group("body"))


def split_instruction(line: str) -> tuple[str, list[str]]:
    operation, operands = line.split(" ", 1)
    return operation, [operand.strip() for operand in operands.split(",")]


def unpack_low(a: tuple[object, ...], b: tuple[object, ...]) -> tuple[object, ...]:
    return a[0], b[0], a[2], b[2]


def unpack_high(a: tuple[object, ...], b: tuple[object, ...]) -> tuple[object, ...]:
    return a[1], b[1], a[3], b[3]


def shuffle_i64x2_ymm(
    a: tuple[object, ...], b: tuple[object, ...], immediate: int
) -> tuple[object, ...]:
    a_start = 2 if immediate & 1 else 0
    b_start = 2 if immediate & 2 else 0
    return a[a_start], a[a_start + 1], b[b_start], b[b_start + 1]


def execute_transpose_macro(lines: list[str]) -> tuple[tuple[object, ...], ...]:
    registers: dict[str, tuple[object, ...]] = {
        f"ymm{row}": tuple((row, column) for column in range(4))
        for row in range(4)
    }
    for line in lines:
        operation, operands = split_instruction(line)
        if operation == "vpunpcklqdq" and len(operands) == 3:
            destination, first, second = operands
            registers[destination] = unpack_low(registers[first], registers[second])
        elif operation == "vpunpckhqdq" and len(operands) == 3:
            destination, first, second = operands
            registers[destination] = unpack_high(registers[first], registers[second])
        elif operation == "vshufi64x2" and len(operands) == 4:
            destination, first, second, immediate = operands
            registers[destination] = shuffle_i64x2_ymm(
                registers[first], registers[second], int(immediate, 0)
            )
        else:
            raise AssertionError(f"unsupported transpose instruction: {line}")
    return tuple(registers[f"ymm{coordinate}"] for coordinate in range(4))


EXPECTED_TRANSPOSE = tuple(
    tuple((lane, coordinate) for lane in range(4)) for coordinate in range(4)
)

POINTER_LOADS = [
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

POINTER_LANES = {
    "rdx": 0,
    "rcx": 1,
    "r8": 2,
    "r9": 3,
    "r10": 4,
    "r11": 5,
    "rdi": 6,
    "rsi": 7,
}


def require_subsequence(lines: list[str], expected: list[str], label: str) -> None:
    cursor = 0
    for line in lines:
        if cursor < len(expected) and line == expected[cursor]:
            cursor += 1
    if cursor != len(expected):
        raise AssertionError(f"{label} differs at expected line {cursor}: {expected[cursor]}")


def parse_calls(lines: list[str]) -> list[list[str]]:
    calls: list[list[str]] = []
    for line in lines:
        if line.startswith("TRANSPOSE_HALF "):
            calls.append([part.strip() for part in line.removeprefix("TRANSPOSE_HALF ").split(",")])
    return calls


def expected_projective_calls() -> list[list[str]]:
    calls: list[list[str]] = []
    for limb in range(5):
        source_offset = 32 * limb
        calls.append([str(source_offset), "0", "rdx", "rcx", "r8", "r9"])
        calls.append([str(source_offset), "32", "r10", "r11", "rdi", "rsi"])
    return calls


def expected_affine_calls() -> list[list[str]]:
    calls: list[list[str]] = []
    for limb in range(5):
        source_offset = 24 * limb
        output_offset = 64 * limb
        calls.append([str(source_offset), str(output_offset), "rdx", "rcx", "r8", "r9"])
        calls.append(
            [str(source_offset), str(output_offset + 32), "r10", "r11", "rdi", "rsi"]
        )
    return calls


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


def certify_projective(text: str) -> None:
    macro = macro_body(text, "TRANSPOSE_4X4")
    if execute_transpose_macro(macro) != EXPECTED_TRANSPOSE:
        raise AssertionError("projective TRANSPOSE_4X4 does not preserve source lane identity")
    if macro_body(text, "TRANSPOSE_HALF") != PROJECTIVE_HALF:
        raise AssertionError("projective TRANSPOSE_HALF load/store layout changed")

    body = function_body(text, "narya_projective_niels_transpose_x8_asm")
    require_subsequence(body, POINTER_LOADS, "projective source-pointer map")
    calls = parse_calls(body)
    if calls != expected_projective_calls():
        raise AssertionError(f"projective limb/half schedule changed: {calls!r}")

    output: dict[tuple[int, int, int], tuple[int, int, int]] = {}
    for source_offset, half, *pointers in calls:
        limb = int(source_offset) // 32
        lane_base = int(half) // 8
        rows = tuple(
            tuple((POINTER_LANES[pointer], limb, coordinate) for coordinate in range(4))
            for pointer in pointers
        )
        transposed = tuple(tuple(rows[lane][coordinate] for lane in range(4)) for coordinate in range(4))
        for coordinate in range(4):
            for local_lane, token in enumerate(transposed[coordinate]):
                output[coordinate, limb, lane_base + local_lane] = token

    for coordinate in range(4):
        for limb in range(5):
            for lane in range(8):
                expected = (lane, limb, coordinate)
                actual = output.get((coordinate, limb, lane))
                if actual != expected:
                    raise AssertionError(
                        f"projective output ({coordinate}, {limb}, {lane}) = {actual}, "
                        f"expected {expected}"
                    )


def certify_affine(text: str) -> None:
    macro = macro_body(text, "TRANSPOSE_4X4")
    if execute_transpose_macro(macro) != EXPECTED_TRANSPOSE:
        raise AssertionError("affine TRANSPOSE_4X4 does not preserve source lane identity")
    if macro_body(text, "TRANSPOSE_HALF") != AFFINE_HALF:
        raise AssertionError("affine TRANSPOSE_HALF masked-load/store layout changed")

    body = function_body(text, "narya_affine_niels_transpose_x8_asm")
    require_subsequence(body, ["mov eax, 7", "kmovb k1, eax", *POINTER_LOADS], "affine mask/pointer map")
    calls = parse_calls(body)
    if calls != expected_affine_calls():
        raise AssertionError(f"affine limb/half schedule changed: {calls!r}")

    output: dict[tuple[int, int, int], tuple[int, int, int]] = {}
    for source_offset, output_offset, *pointers in calls:
        limb = int(source_offset) // 24
        lane_base = (int(output_offset) % 64) // 8
        rows = tuple(
            tuple((POINTER_LANES[pointer], limb, coordinate) for coordinate in range(3))
            + (None,)
            for pointer in pointers
        )
        transposed = tuple(tuple(rows[lane][coordinate] for lane in range(4)) for coordinate in range(4))
        for coordinate in range(3):
            for local_lane, token in enumerate(transposed[coordinate]):
                output[coordinate, limb, lane_base + local_lane] = token

    for coordinate in range(3):
        for limb in range(5):
            for lane in range(8):
                expected = (lane, limb, coordinate)
                actual = output.get((coordinate, limb, lane))
                if actual != expected:
                    raise AssertionError(
                        f"affine output ({coordinate}, {limb}, {lane}) = {actual}, expected {expected}"
                    )


def main() -> None:
    projective_path = ROOT / "src/projective_niels_transpose_x8.S"
    affine_path = ROOT / "src/affine_niels_transpose_x8.S"
    projective = projective_path.read_text(encoding="ascii")
    affine = affine_path.read_text(encoding="ascii")

    projective_macro = macro_body(projective, "TRANSPOSE_4X4")
    affine_macro = macro_body(affine, "TRANSPOSE_4X4")
    if projective_macro != affine_macro:
        raise AssertionError("projective and affine transpose networks diverged")

    certify_projective(projective)
    certify_affine(affine)
    print("OK: projective x8 transpose preserves all 8 lanes, 5 limbs, and 4 coordinates")
    print("OK: affine x8 transpose preserves all 8 lanes, 5 limbs, and 3 coordinates")


if __name__ == "__main__":
    main()
