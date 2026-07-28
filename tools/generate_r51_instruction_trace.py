#!/usr/bin/env python3
"""Generate the expanded r51 multiplier instruction trace from assembly source.

This is the source-side half of the binary refinement check. The exact linked
bytes are decoded independently in Lean and must equal this expanded list.
The generator reuses the strict source parser from generate_r51_mul_trace.py;
it is not an x86 decoder and is intentionally kept separate from the byte-side
decoder.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

from generate_r51_mul_trace import SOURCE, fail, function_body, render, source_statements


ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "formal/lean/NaryaFormal/GeneratedR51InstructionTrace.lean"

# These are mathematical schedule phases, not arbitrary formatting chunks.
# Keep the boundary assertions below: a source edit must be classified before
# it can silently move across a proof boundary.
PHASES = (
    ("loadPhase", 0, 10),
    ("clearPhase", 10, 28),
    ("productPhase", 28, 78),
    ("combinePhase", 78, 95),
    ("foldPhase", 95, 106),
    ("normalizePhase", 106, 122),
    ("storePhase", 122, 127),
    ("epiloguePhase", 127, 129),
)


def zmm(value: str | int) -> str:
    number = int(value)
    if not 0 <= number < 32:
        fail(f"ZMM register outside architectural range: {number}")
    return f"⟨{number}, by decide⟩"


def ternary(name: str, destination: str, source1: str, source2: str) -> str:
    return f".{name} {zmm(destination)} {zmm(source1)} {zmm(source2)}"


def expand_statement(statement: str) -> list[str]:
    match = re.fullmatch(
        r"vmovdqu64 zmm(\d+), ZMMWORD PTR \[(rsi|rdx) \+ (\d+)\]", statement
    )
    if match:
        register, base, displacement = match.groups()
        return [f".vmovdqu64Load {zmm(register)} .{base} {int(displacement)}"]

    match = re.fullmatch(
        r"vmovdqu64 ZMMWORD PTR \[rdi \+ (\d+)\], zmm(\d+)", statement
    )
    if match:
        displacement, register = match.groups()
        return [f".vmovdqu64Store .rdi {int(displacement)} {zmm(register)}"]

    match = re.fullmatch(r"CLEAR zmm(\d+)", statement)
    if match:
        register = match.group(1)
        return [ternary("vpxorq", register, register, register)]

    match = re.fullmatch(
        r"MUL_PAIR zmm(\d+), zmm(\d+), zmm(\d+), zmm(\d+)", statement
    )
    if match:
        x, y, low, high = match.groups()
        return [
            ternary("vpmadd52luq", low, x, y),
            ternary("vpmadd52huq", high, x, y),
        ]

    match = re.fullmatch(r"COMBINE_HIGH zmm(\d+), zmm(\d+)", statement)
    if match:
        high, low = match.groups()
        return [
            f".vpsllq {zmm(high)} {zmm(high)} 1",
            ternary("vpaddq", low, low, high),
        ]

    match = re.fullmatch(r"vpsllq zmm(\d+), zmm(\d+), (\d+)", statement)
    if match:
        destination, source, amount = match.groups()
        return [f".vpsllq {zmm(destination)} {zmm(source)} {int(amount)}"]

    match = re.fullmatch(
        r"vpbroadcastq zmm(\d+), QWORD PTR \[rip \+ narya_ifma_(fold19|mask51)\]",
        statement,
    )
    if match:
        register, constant = match.groups()
        address = {
            "fold19": "R51Object.ifma_fold19Address",
            "mask51": "R51Object.ifma_mask51Address",
        }[constant]
        return [f".vpbroadcastq {zmm(register)} {address}"]

    match = re.fullmatch(
        r"FOLD_INTO zmm(\d+), zmm(\d+), zmm(\d+), zmm(\d+)", statement
    )
    if match:
        low, high, temporary, fold = match.groups()
        return [
            ternary("vpmullq", temporary, high, fold),
            ternary("vpaddq", low, low, temporary),
        ]

    match = re.fullmatch(r"NORMALIZE_5 (.+)", statement)
    if match:
        arguments = [
            item.strip().removeprefix("zmm") for item in match.group(1).split(",")
        ]
        if len(arguments) != 12 or any(not item.isdigit() for item in arguments):
            fail(f"invalid NORMALIZE_5 arguments: {statement!r}")
        in0, in1, in2, in3, in4, mask, c0, c1, c2, c3, c4, fold = arguments
        inputs = [in0, in1, in2, in3, in4]
        carries = [c0, c1, c2, c3, c4]
        result = [
            f".vpsrlq {zmm(carry)} {zmm(value)} 51"
            for carry, value in zip(carries, inputs)
        ]
        result.extend(
            ternary("vpandq", value, value, mask) for value in inputs
        )
        result.extend(
            ternary("vpaddq", inputs[index], inputs[index], carries[index - 1])
            for index in range(1, 5)
        )
        result.append(ternary("vpmadd52luq", in0, fold, c4))
        return result

    if statement == "vzeroupper":
        return [".vzeroUpper"]
    if statement == "ret":
        return [".ret"]

    fail(f"unmodeled expanded instruction statement: {statement!r}")


def render_instruction_list(name: str, instructions: list[str]) -> list[str]:
    lines = [f"def {name} : List Instruction := ["]
    lines.extend(f"  {instruction}," for instruction in instructions[:-1])
    lines.append(f"  {instructions[-1]}")
    lines.extend(["]", ""])
    return lines


def generate() -> str:
    source = SOURCE.read_text(encoding="ascii")
    # Reuse every source-shape, register, constant, and range-routing check in
    # the existing arithmetic extractor before emitting the instruction list.
    render(source)
    body = function_body(source, "narya_r51x8_mul_ifma")
    instructions: list[str] = []
    for statement in source_statements(body):
        instructions.extend(expand_statement(statement))
    if len(instructions) != 129:
        fail(f"expanded instruction count changed: {len(instructions)} != 129")

    phase_instructions: dict[str, list[str]] = {
        name: instructions[start:end] for name, start, end in PHASES
    }
    if [item for name, _, _ in PHASES for item in phase_instructions[name]] != instructions:
        fail("proof-phase boundaries no longer partition the instruction trace")

    expected_phase_shapes = {
        "loadPhase": {".vmovdqu64Load"},
        "clearPhase": {".vpxorq"},
        "productPhase": {".vpmadd52luq", ".vpmadd52huq"},
        "combinePhase": {".vpsllq", ".vpaddq"},
        "foldPhase": {".vpbroadcastq", ".vpmullq", ".vpaddq"},
        "normalizePhase": {".vpbroadcastq", ".vpsrlq", ".vpandq", ".vpaddq", ".vpmadd52luq"},
        "storePhase": {".vmovdqu64Store"},
        "epiloguePhase": {".vzeroUpper", ".ret"},
    }
    for name, phase in phase_instructions.items():
        opcodes = {instruction.split(maxsplit=1)[0] for instruction in phase}
        if not opcodes <= expected_phase_shapes[name]:
            fail(f"{name} has an instruction outside its proof vocabulary: {sorted(opcodes)}")

    lines = [
        "/-",
        "Copyright 2026 Overclock Validator",
        "SPDX-License-Identifier: Apache-2.0",
        "",
        "GENERATED FILE. DO NOT EDIT.",
        "Generated from src/r51x8_ifma.S by",
        "tools/generate_r51_instruction_trace.py.",
        "This is the source-side instruction trace, not an x86 decoder.",
        "-/",
        "",
        "import NaryaFormal.X86Decoder",
        "",
        "namespace NaryaFormal.X86.GeneratedR51InstructionTrace",
        "",
    ]
    for name, _, _ in PHASES:
        lines.extend(render_instruction_list(name, phase_instructions[name]))
    lines.extend(
        [
            "def expectedProgram : List Instruction :=",
            "  loadPhase ++ clearPhase ++ productPhase ++ combinePhase ++",
            "  foldPhase ++ normalizePhase ++ storePhase ++ epiloguePhase",
            "",
            "set_option maxRecDepth 4096 in",
            "theorem phase_lengths :",
            "    loadPhase.length = 10 ∧ clearPhase.length = 18 ∧",
            "    productPhase.length = 50 ∧ combinePhase.length = 17 ∧",
            "    foldPhase.length = 11 ∧ normalizePhase.length = 16 ∧",
            "    storePhase.length = 5 ∧ epiloguePhase.length = 2 := by",
            "  decide",
            "",
            "set_option maxRecDepth 4096 in",
            "theorem expected_instruction_count : expectedProgram.length = 129 := by",
            "  decide",
            "",
            "end NaryaFormal.X86.GeneratedR51InstructionTrace",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    generated = generate()
    if arguments.check:
        committed = GENERATED.read_text(encoding="utf-8")
        if committed != generated:
            sys.stderr.writelines(
                difflib.unified_diff(
                    committed.splitlines(keepends=True),
                    generated.splitlines(keepends=True),
                    fromfile=str(GENERATED.relative_to(ROOT)),
                    tofile="generated from src/r51x8_ifma.S",
                )
            )
            raise SystemExit(1)
        print("OK: r51 source instruction trace matches committed Lean input")
    elif arguments.output is not None:
        arguments.output.write_text(generated, encoding="utf-8")
    else:
        print(generated, end="")


if __name__ == "__main__":
    main()
