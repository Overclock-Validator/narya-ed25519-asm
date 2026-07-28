#!/usr/bin/env python3
"""Generate the Lean r51 multiply trace from the checked assembly source.

This is deliberately a small source-level extractor, not an x86 decoder.  It
accepts only the macro bodies and straight-line SysV leaf shape that the Lean
semantics model.  The generated definitions are consumed by AssemblyTrace.lean,
so changing an accumulator target, combine, fold, normalize argument, or store
either changes a proof input or makes extraction fail closed.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/r51x8_ifma.S"
GENERATED = ROOT / "formal/lean/NaryaFormal/GeneratedR51MulTrace.lean"


def fail(message: str) -> NoReturn:
    raise SystemExit(f"r51 multiply trace extraction failed: {message}")


def function_body(source: str, symbol: str) -> str:
    match = re.search(
        rf"(?ms)^{re.escape(symbol)}:\s*$(.*?)^\.size\s+{re.escape(symbol)},",
        source,
    )
    if match is None:
        fail(f"missing function body for {symbol}")
    return match.group(1)


def macro_body(source: str, name: str) -> list[str]:
    match = re.search(
        rf"(?ms)^\.macro\s+{re.escape(name)}\b[^\n]*\n(.*?)^\.endm\s*$", source
    )
    if match is None:
        fail(f"missing macro {name}")
    result: list[str] = []
    in_comment = False
    for raw in match.group(1).splitlines():
        line = raw.strip()
        if "/*" in line:
            in_comment = True
        if not in_comment and line:
            result.append(re.sub(r"\s+", " ", line))
        if "*/" in line:
            in_comment = False
    return result


def require_macro(source: str, name: str, expected: list[str]) -> None:
    actual = macro_body(source, name)
    if actual != expected:
        fail(f"macro {name} changed\nexpected={expected!r}\nactual={actual!r}")


def parse_int(value: str) -> int:
    return int(value, 0)


def source_statements(body: str) -> list[str]:
    """Return every non-comment statement, joining GAS continuations."""

    without_comments = re.sub(r"/\*.*?\*/", "", body, flags=re.DOTALL)
    result: list[str] = []
    pending = ""
    for raw in without_comments.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.endswith("\\"):
            pending += line[:-1].strip() + " "
            continue
        result.append(re.sub(r"\s+", " ", pending + line))
        pending = ""
    if pending:
        fail("unterminated assembly line continuation")
    return result


@dataclass(frozen=True)
class Product:
    x: int
    y: int


def list_expression(kind: str, products: list[Product]) -> str:
    if not products:
        return "[]"
    return "[" + ", ".join(f"{kind} (x {p.x}) (y {p.y})" for p in products) + "]"


def sum_expression(items: list[str]) -> str:
    if not items:
        return "0"
    return " + ".join(items)


def render(source: str) -> str:
    require_macro(source, "CLEAR", [r"vpxorq \r, \r, \r"])
    require_macro(
        source,
        "MUL_PAIR",
        [
            r"vpmadd52luq \l, \x, \y",
            r"vpmadd52huq \h, \x, \y",
        ],
    )
    require_macro(
        source,
        "COMBINE_HIGH",
        [r"vpsllq \h, \h, 1", r"vpaddq \l, \l, \h"],
    )
    require_macro(
        source,
        "FOLD_INTO",
        [r"vpmullq \tmp, \hi, \fold19", r"vpaddq \lo, \lo, \tmp"],
    )
    require_macro(
        source,
        "NORMALIZE_5",
        [
            r"vpsrlq \c0, \in0, 51",
            r"vpsrlq \c1, \in1, 51",
            r"vpsrlq \c2, \in2, 51",
            r"vpsrlq \c3, \in3, 51",
            r"vpsrlq \c4, \in4, 51",
            r"vpandq \in0, \in0, \mask",
            r"vpandq \in1, \in1, \mask",
            r"vpandq \in2, \in2, \mask",
            r"vpandq \in3, \in3, \mask",
            r"vpandq \in4, \in4, \mask",
            r"vpaddq \in1, \in1, \c0",
            r"vpaddq \in2, \in2, \c1",
            r"vpaddq \in3, \in3, \c2",
            r"vpaddq \in4, \in4, \c3",
            r"vpmadd52luq \in0, \fold19, \c4",
        ],
    )

    body = function_body(source, "narya_r51x8_mul_ifma")
    statements = source_statements(body)
    allowed_statements = [
        re.compile(r"vmovdqu64 zmm\d+, ZMMWORD PTR \[(?:rsi|rdx) \+ \d+\]"),
        re.compile(r"CLEAR zmm\d+"),
        re.compile(r"MUL_PAIR zmm\d+, zmm\d+, zmm\d+, zmm\d+"),
        re.compile(r"COMBINE_HIGH zmm\d+, zmm\d+"),
        re.compile(r"vpsllq zmm\d+, zmm\d+, \d+"),
        re.compile(r"vpbroadcastq zmm\d+, QWORD PTR \[rip \+ narya_ifma_\w+\]"),
        re.compile(r"FOLD_INTO zmm\d+, zmm\d+, zmm\d+, zmm\d+"),
        re.compile(
            r"NORMALIZE_5 zmm\d+(?:, zmm\d+){5}, zmm\d+(?:, zmm\d+){5}"
        ),
        re.compile(r"vmovdqu64 ZMMWORD PTR \[rdi \+ \d+\], zmm\d+"),
        re.compile(r"vzeroupper"),
        re.compile(r"ret"),
    ]
    for statement in statements:
        if not any(pattern.fullmatch(statement) for pattern in allowed_statements):
            fail(f"unmodeled instruction or directive in multiply leaf: {statement!r}")

    def phase(statement: str) -> str:
        if statement.startswith("vmovdqu64 zmm"):
            return "load"
        if statement.startswith("CLEAR"):
            return "clear"
        if statement.startswith("MUL_PAIR"):
            return "multiply"
        if statement.startswith("COMBINE_HIGH"):
            return "combine"
        if statement.startswith("vpsllq"):
            return "top-shift"
        if "narya_ifma_fold19" in statement:
            return "fold-broadcast"
        if statement.startswith("FOLD_INTO"):
            return "fold"
        if "narya_ifma_mask51" in statement:
            return "mask-broadcast"
        if statement.startswith("NORMALIZE_5"):
            return "normalize"
        if statement.startswith("vmovdqu64 ZMMWORD PTR [rdi"):
            return "store"
        if statement == "vzeroupper":
            return "vzeroupper"
        if statement == "ret":
            return "ret"
        fail(f"internal phase classification omitted {statement!r}")

    expected_phases = (
        ["load"] * 10
        + ["clear"] * 18
        + ["multiply"] * 25
        + ["combine"] * 8
        + ["top-shift", "fold-broadcast"]
        + ["fold"] * 5
        + ["mask-broadcast", "normalize"]
        + ["store"] * 5
        + ["vzeroupper", "ret"]
    )
    actual_phases = [phase(statement) for statement in statements]
    if actual_phases != expected_phases:
        fail(f"multiply leaf phase/order changed: {actual_phases!r}")

    register_input: dict[int, tuple[str, int]] = {}
    load_pattern = re.compile(
        r"^\s*vmovdqu64\s+zmm(\d+),\s+ZMMWORD PTR \[(rsi|rdx)\s*\+\s*(\d+)\]",
        re.MULTILINE,
    )
    for register, base, offset in load_pattern.findall(body):
        limb_offset = int(offset)
        if limb_offset % 64 != 0 or limb_offset > 256:
            fail(f"invalid source offset {limb_offset}")
        register_input[int(register)] = ("x" if base == "rsi" else "y", limb_offset // 64)
    expected_inputs = {
        **{i: ("x", i) for i in range(5)},
        **{i + 5: ("y", i) for i in range(5)},
    }
    if register_input != expected_inputs:
        fail(f"source load map changed: {register_input!r}")
    load_statement_indices = [
        index for index, statement in enumerate(statements)
        if statement.startswith("vmovdqu64 zmm")
    ]
    first_product_index = next(
        (index for index, statement in enumerate(statements) if statement.startswith("MUL_PAIR")),
        None,
    )
    first_store_index = next(
        (index for index, statement in enumerate(statements)
         if statement.startswith("vmovdqu64 ZMMWORD PTR [rdi")),
        None,
    )
    if (
        len(load_statement_indices) != 10
        or first_product_index is None
        or first_store_index is None
        or max(load_statement_indices) >= first_product_index
        or max(load_statement_indices) >= first_store_index
    ):
        fail("all ten source vectors must load before arithmetic and stores")

    clear_registers = [
        int(value)
        for value in re.findall(r"^\s*CLEAR\s+zmm(\d+)\s*$", body, re.MULTILINE)
    ]
    if clear_registers != list(range(10, 28)):
        fail(f"accumulator clear map changed: {clear_registers!r}")

    low_products: dict[int, list[Product]] = {degree: [] for degree in range(9)}
    high_products: dict[int, list[Product]] = {degree: [] for degree in range(9)}
    pairs = re.findall(
        r"^\s*MUL_PAIR\s+zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+)\s*$",
        body,
        re.MULTILINE,
    )
    if len(pairs) != 25:
        fail(f"expected 25 MUL_PAIR updates, found {len(pairs)}")
    seen: list[Product] = []
    for xreg_text, yreg_text, lowreg_text, highreg_text in pairs:
        xreg, yreg = int(xreg_text), int(yreg_text)
        lowreg, highreg = int(lowreg_text), int(highreg_text)
        if xreg not in register_input or yreg not in register_input:
            fail(f"MUL_PAIR uses an unloaded register: zmm{xreg}, zmm{yreg}")
        xsource, xlimb = register_input[xreg]
        ysource, ylimb = register_input[yreg]
        if xsource != "x" or ysource != "y":
            fail(f"MUL_PAIR source orientation changed: zmm{xreg}, zmm{yreg}")
        low_degree, high_degree = lowreg - 10, highreg - 19
        if low_degree not in low_products or high_degree not in high_products:
            fail(f"MUL_PAIR accumulator outside modeled range: zmm{lowreg}, zmm{highreg}")
        product = Product(xlimb, ylimb)
        low_products[low_degree].append(product)
        high_products[high_degree].append(product)
        seen.append(product)
    expected_products = {Product(i, j) for i in range(5) for j in range(5)}
    if set(seen) != expected_products or len(set(seen)) != 25:
        fail("MUL_PAIR trace is not a complete, duplicate-free 5x5 product set")

    # Symbolically execute the macro-level accumulator schedule.  Expressions
    # refer to the generated source-ordered term lists below.
    registers: dict[int, str] = {}
    for degree in range(9):
        registers[10 + degree] = f"(lowTerms x y {degree}).sum"
        registers[19 + degree] = f"(highTerms x y {degree}).sum"

    combines = [
        (int(high), int(low))
        for high, low in re.findall(
            r"^\s*COMBINE_HIGH\s+zmm(\d+),\s*zmm(\d+)\s*$",
            body,
            re.MULTILINE,
        )
    ]
    if len(combines) != 8:
        fail(f"expected 8 COMBINE_HIGH calls, found {len(combines)}")
    for high, low in combines:
        if high not in registers or low not in registers:
            fail(f"COMBINE_HIGH uses an unknown accumulator: zmm{high}, zmm{low}")
        registers[high] = f"2 * ({registers[high]})"
        registers[low] = f"({registers[low]}) + ({registers[high]})"

    shifts = re.findall(
        r"^\s*vpsllq\s+zmm(\d+),\s*zmm(\d+),\s*(\d+)\s*$",
        body,
        re.MULTILINE,
    )
    if shifts != [("27", "27", "1")]:
        fail(f"terminal high-half shift changed: {shifts!r}")
    registers[27] = f"2 * ({registers[27]})"

    grouped_registers = [10 + degree for degree in range(9)] + [27]
    grouped_expressions = [registers[register] for register in grouped_registers]

    constant_pattern = re.compile(
        r"(?ms)^narya_ifma_(mask51|fold19):\s*\n\s*\.quad\s+([^\s]+)"
    )
    constants = {name: parse_int(value) for name, value in constant_pattern.findall(source)}
    if set(constants) != {"mask51", "fold19"}:
        fail(f"missing field constants: {constants!r}")

    broadcasts = re.findall(
        r"^\s*vpbroadcastq\s+zmm(\d+),\s+QWORD PTR \[rip \+ narya_ifma_(\w+)\]\s*$",
        body,
        re.MULTILINE,
    )
    if broadcasts != [("30", "fold19"), ("5", "mask51")]:
        fail(f"constant broadcast schedule changed: {broadcasts!r}")

    folds = [
        tuple(map(int, values))
        for values in re.findall(
            r"^\s*FOLD_INTO\s+zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+)\s*$",
            body,
            re.MULTILINE,
        )
    ]
    if len(folds) != 5:
        fail(f"expected 5 FOLD_INTO calls, found {len(folds)}")
    for low, high, temporary, constant_register in folds:
        if low not in registers or high not in registers:
            fail(f"FOLD_INTO uses an unknown accumulator: zmm{low}, zmm{high}")
        if temporary in (low, high, constant_register) or constant_register != 30:
            fail(f"invalid fold register contract: {(low, high, temporary, constant_register)!r}")
        registers[low] = f"({registers[low]}) + foldConstant * ({registers[high]})"

    normalize_match = re.search(
        r"(?ms)^\s*NORMALIZE_5\s+zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*\\\s*\n\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+),\s*zmm(\d+)\s*$",
        body,
    )
    if normalize_match is None:
        fail("missing NORMALIZE_5 call")
    normalize = tuple(map(int, normalize_match.groups()))
    inputs = normalize[:5]
    mask_register = normalize[5]
    carries = normalize[6:11]
    fold_register = normalize[11]
    if len(set(inputs + carries + (mask_register, fold_register))) != 12:
        fail(f"NORMALIZE_5 register alias changed: {normalize!r}")
    if mask_register != 5 or fold_register != 30:
        fail(f"NORMALIZE_5 constant registers changed: {normalize!r}")
    for register in inputs:
        if register not in registers:
            fail(f"NORMALIZE_5 uses unknown input zmm{register}")

    pre_normalize = [registers[register] for register in inputs]
    normalized = [
        f"traceRemainder ({pre_normalize[0]}) + lo52 foldConstant (traceCarry ({pre_normalize[4]}))",
        f"traceRemainder ({pre_normalize[1]}) + traceCarry ({pre_normalize[0]})",
        f"traceRemainder ({pre_normalize[2]}) + traceCarry ({pre_normalize[1]})",
        f"traceRemainder ({pre_normalize[3]}) + traceCarry ({pre_normalize[2]})",
        f"traceRemainder ({pre_normalize[4]}) + traceCarry ({pre_normalize[3]})",
    ]
    if len(inputs) != len(normalized):
        fail("internal normalize arity mismatch")
    for register, expression in zip(inputs, normalized):
        registers[register] = expression

    stores = [
        (int(offset), int(register))
        for offset, register in re.findall(
            r"^\s*vmovdqu64\s+ZMMWORD PTR \[rdi\s*\+\s*(\d+)\],\s*zmm(\d+)\s*$",
            body,
            re.MULTILINE,
        )
    ]
    if len(stores) != 5:
        fail(f"expected 5 output stores, found {len(stores)}")
    output_expressions: list[str] = []
    for expected_offset in range(0, 320, 64):
        matches = [register for offset, register in stores if offset == expected_offset]
        if len(matches) != 1 or matches[0] not in registers:
            fail(f"invalid output store for offset {expected_offset}: {matches!r}")
        output_expressions.append(registers[matches[0]])

    if not re.search(r"(?m)^\s*vzeroupper\s*\n\s*ret\s*$", body):
        fail("function epilogue changed")

    lines = [
        "/-",
        "Copyright 2026 Overclock Validator",
        "SPDX-License-Identifier: Apache-2.0",
        "",
        "GENERATED FILE. DO NOT EDIT.",
        "Generated by tools/generate_r51_mul_trace.py from src/r51x8_ifma.S.",
        "The definitions below are proof inputs, not an independent oracle.",
        "-/",
        "",
        "import NaryaFormal.Radix51",
        "",
        "namespace NaryaFormal.Radix51.GeneratedR51MulTrace",
        "",
        f"def sourceLoadOffsets : List Nat := {[i * 64 for i in range(5)]!r}",
        f"def outputStoreOffsets : List Nat := {[offset for offset, _ in stores]!r}",
        f"def foldConstant : Nat := {constants['fold19']}",
        f"def traceMask : Nat := {constants['mask51']}",
        "def traceCarry (value : Nat) : Nat := value / (2 ^ 51)",
        "def traceRemainder (value : Nat) : Nat := value % (2 ^ 51)",
        "",
        "def lowTerms (x y : FiveLimbs) : Nat -> List Nat",
    ]
    for degree in range(9):
        lines.append(f"  | {degree} => {list_expression('lo52', low_products[degree])}")
    lines.extend(["  | _ => []", "", "def highTerms (x y : FiveLimbs) : Nat -> List Nat"])
    for degree in range(9):
        lines.append(f"  | {degree} => {list_expression('hi52', high_products[degree])}")
    lines.extend(["  | _ => []", "", "def groupedDegree (x y : FiveLimbs) : Nat -> Nat"])
    for degree, expression in enumerate(grouped_expressions):
        lines.append(f"  | {degree} => {expression}")
    lines.extend(
        [
            "  | _ => 0",
            "",
            "def foldedGrouped (x y : FiveLimbs) : Loose5 :=",
            "  { l0 := " + pre_normalize[0],
            "    l1 := " + pre_normalize[1],
            "    l2 := " + pre_normalize[2],
            "    l3 := " + pre_normalize[3],
            "    l4 := " + pre_normalize[4] + " }",
            "",
            "def assemblyOutput (x y : FiveLimbs) : Loose5 :=",
            "  { l0 := " + output_expressions[0],
            "    l1 := " + output_expressions[1],
            "    l2 := " + output_expressions[2],
            "    l3 := " + output_expressions[3],
            "    l4 := " + output_expressions[4] + " }",
            "",
            "end NaryaFormal.Radix51.GeneratedR51MulTrace",
            "",
        ]
    )
    # Python list repr uses commas exactly as Lean accepts for Nat literals.
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument(
        "--check",
        action="store_true",
        help="require the committed generated Lean file to match the source",
    )
    arguments = parser.parse_args()
    generated = render(arguments.source.read_text(encoding="ascii"))
    if not arguments.check:
        print(generated, end="")
        return

    committed = GENERATED.read_text(encoding="ascii")
    if committed != generated:
        print(
            "generated r51 multiply trace differs from the committed Lean input",
            file=sys.stderr,
        )
        sys.stderr.writelines(
            difflib.unified_diff(
                committed.splitlines(keepends=True),
                generated.splitlines(keepends=True),
                fromfile=str(GENERATED.relative_to(ROOT)),
                tofile="generated from src/r51x8_ifma.S",
            )
        )
        raise SystemExit(1)
    print("OK: r51 multiply assembly source matches generated Lean trace")


if __name__ == "__main__":
    main()
