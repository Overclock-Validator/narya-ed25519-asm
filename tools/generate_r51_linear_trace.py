#!/usr/bin/env python3
"""Generate the Lean trace for the r51 x8 linear field leaves.

This is a deliberately strict source-level extractor, not an x86 decoder.  It
accepts only the straight-line add, subtract, and negate leaves whose scalar
semantics are modeled by ``LinearTrace.lean``.  Any opcode, operand, constant,
normalization, load/store mapping, or instruction-order change must either
change the generated Lean proof input or make extraction fail closed.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path
from typing import NoReturn


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/r51x8_ifma.S"
GENERATED = ROOT / "formal/lean/NaryaFormal/GeneratedR51LinearTrace.lean"


def fail(message: str) -> NoReturn:
    raise SystemExit(f"r51 linear trace extraction failed: {message}")


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


def source_statements(body: str) -> list[str]:
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


def require_equal(name: str, actual: object, expected: object) -> None:
    if actual != expected:
        fail(f"{name} changed\nexpected={expected!r}\nactual={actual!r}")


def load(base: str, limb: int, register: int) -> str:
    return f"vmovdqu64 zmm{register}, ZMMWORD PTR [{base} + {64 * limb}]"


def memory_op(opcode: str, register: int, base: str, limb: int) -> str:
    return f"{opcode} zmm{register}, zmm{register}, ZMMWORD PTR [{base} + {64 * limb}]"


def store(limb: int, register: int) -> str:
    return f"vmovdqu64 ZMMWORD PTR [rdi + {64 * limb}], zmm{register}"


NORMALIZE = (
    "NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, "
    "zmm6, zmm7, zmm8, zmm9, zmm10, zmm11"
)


def check_macro(source: str) -> None:
    expected = [
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
    ]
    require_equal("NORMALIZE_5 macro", macro_body(source, "NORMALIZE_5"), expected)


def check_functions(source: str) -> None:
    common_tail = [
        "vpbroadcastq zmm5, QWORD PTR [rip + narya_ifma_mask51]",
        "vpbroadcastq zmm11, QWORD PTR [rip + narya_ifma_fold19]",
        NORMALIZE,
        *[store(i, i) for i in range(5)],
        "vzeroupper",
        "ret",
    ]

    add = (
        [load("rsi", i, i) for i in range(5)]
        + [memory_op("vpaddq", i, "rdx", i) for i in range(5)]
        + common_tail
    )
    require_equal(
        "narya_r51x8_add_ifma instruction trace",
        source_statements(function_body(source, "narya_r51x8_add_ifma")),
        add,
    )

    sub = (
        [load("rsi", i, i) for i in range(5)]
        + [
            "vpbroadcastq zmm9, QWORD PTR [rip + narya_ifma_sub_bias0]",
            "vpbroadcastq zmm10, QWORD PTR [rip + narya_ifma_sub_biasn]",
            "vpaddq zmm0, zmm0, zmm9",
            "vpaddq zmm1, zmm1, zmm10",
            "vpaddq zmm2, zmm2, zmm10",
            "vpaddq zmm3, zmm3, zmm10",
            "vpaddq zmm4, zmm4, zmm10",
        ]
        + [memory_op("vpsubq", i, "rdx", i) for i in range(5)]
        + common_tail
    )
    require_equal(
        "narya_r51x8_sub_ifma instruction trace",
        source_statements(function_body(source, "narya_r51x8_sub_ifma")),
        sub,
    )

    neg = [
        "vpbroadcastq zmm0, QWORD PTR [rip + narya_ifma_sub_bias0]",
        "vpbroadcastq zmm1, QWORD PTR [rip + narya_ifma_sub_biasn]",
        "vmovdqa64 zmm2, zmm1",
        "vmovdqa64 zmm3, zmm1",
        "vmovdqa64 zmm4, zmm1",
        *[memory_op("vpsubq", i, "rsi", i) for i in range(5)],
        *common_tail,
    ]
    require_equal(
        "narya_r51x8_neg_ifma instruction trace",
        source_statements(function_body(source, "narya_r51x8_neg_ifma")),
        neg,
    )


def constant(source: str, symbol: str) -> int:
    match = re.search(
        rf"(?m)^{re.escape(symbol)}:\s*\n\s*\.quad\s+(0x[0-9a-fA-F]+|[0-9]+)\s*$",
        source,
    )
    if match is None:
        fail(f"missing scalar constant {symbol}")
    return int(match.group(1), 0)


def render(source: str) -> str:
    check_macro(source)
    check_functions(source)

    mask = constant(source, "narya_ifma_mask51")
    fold = constant(source, "narya_ifma_fold19")
    bias0 = constant(source, "narya_ifma_sub_bias0")
    biasn = constant(source, "narya_ifma_sub_biasn")

    return f"""/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Generated by tools/generate_r51_linear_trace.py from src/r51x8_ifma.S.
Do not edit by hand. The generator accepts only the exact straight-line add,
subtract, negate, NORMALIZE_5, load/store, and constant shapes modeled here.
This is a source trace, not an emitted-object or x86 ISA refinement.
-/

import NaryaFormal.Radix51

namespace NaryaFormal.Radix51.GeneratedR51LinearTrace

def sourceMask : Nat := {mask}
def sourceFold : Nat := {fold}
def sourceBias0 : Nat := {bias0}
def sourceBiasN : Nat := {biasn}

def addRaw (x y : Loose5) : Loose5 :=
  {{ l0 := x.l0 + y.l0
    l1 := x.l1 + y.l1
    l2 := x.l2 + y.l2
    l3 := x.l3 + y.l3
    l4 := x.l4 + y.l4 }}

def subRaw (x y : Loose5) : Loose5 :=
  {{ l0 := x.l0 + sourceBias0 - y.l0
    l1 := x.l1 + sourceBiasN - y.l1
    l2 := x.l2 + sourceBiasN - y.l2
    l3 := x.l3 + sourceBiasN - y.l3
    l4 := x.l4 + sourceBiasN - y.l4 }}

def negRaw (x : Loose5) : Loose5 :=
  {{ l0 := sourceBias0 - x.l0
    l1 := sourceBiasN - x.l1
    l2 := sourceBiasN - x.l2
    l3 := sourceBiasN - x.l3
    l4 := sourceBiasN - x.l4 }}

def addOutput (x y : Loose5) : Loose5 := normalized (addRaw x y)
def subOutput (x y : Loose5) : Loose5 := normalized (subRaw x y)
def negOutput (x : Loose5) : Loose5 := normalized (negRaw x)

end NaryaFormal.Radix51.GeneratedR51LinearTrace
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()

    generated = render(arguments.source.read_text(encoding="ascii"))
    if arguments.output is not None:
        arguments.output.write_text(generated, encoding="ascii")
        return
    if arguments.check:
        committed = GENERATED.read_text(encoding="ascii")
        if committed != generated:
            sys.stderr.writelines(
                difflib.unified_diff(
                    committed.splitlines(keepends=True),
                    generated.splitlines(keepends=True),
                    fromfile=str(GENERATED),
                    tofile="generated",
                )
            )
            fail("generated Lean trace differs from the committed artifact")
        print("OK: r51 add/sub/neg source trace matches committed Lean input")
        return
    sys.stdout.write(generated)


if __name__ == "__main__":
    main()
