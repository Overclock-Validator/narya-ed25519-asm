#!/usr/bin/env python3
"""Source-level signed-range certificate for scalar_reduce_x8.S.

The checker parses the actual FOLD/CARRY macro call sequence and propagates
arbitrary-precision integer intervals through every machine operation. It
fails if a signed add, subtract, multiply, bias, or reconstructed carry could
leave int64, or if the checked macro/constant/load/store templates drift.

This certificate proves machine-range safety and modular preservation of the
exact source schedule. It also establishes the source-level checkpoint bound
used by the separate Lean canonical-tail theorem. It does not prove the C
parser/packer or assembled-binary instruction refinement.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/scalar_reduce_x8.S"

B = 1 << 21
ROUND = 1 << 20
I64_MIN = -(1 << 63)
I64_MAX = (1 << 63) - 1
L = (1 << 252) + 27742317777372353535851937790883648493

FOLD_CONSTANTS = (666643, 470296, 654183, 997805, 136657, 683901)
FOLD_SIGNS = (1, 1, 1, -1, 1, -1)


@dataclass(frozen=True)
class Interval:
    lower: int
    upper: int

    def add(self, other: "Interval") -> "Interval":
        return Interval(self.lower + other.lower, self.upper + other.upper)

    def subtract(self, other: "Interval") -> "Interval":
        return Interval(self.lower - other.upper, self.upper - other.lower)

    def multiply_constant(self, constant: int) -> "Interval":
        products = (self.lower * constant, self.upper * constant)
        return Interval(min(products), max(products))

    def floor_divide(self, divisor: int) -> "Interval":
        return Interval(self.lower // divisor, self.upper // divisor)


def strip_comments(text: str) -> str:
    return re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)


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
    clean = strip_comments(text)
    match = re.search(
        rf"^{re.escape(symbol)}:\n(?P<body>.*?)^\.size {re.escape(symbol)},",
        clean,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise AssertionError(f"missing function {symbol}")
    return normalized_lines(match.group("body"))


FOLD_MACRO = [
    r"vpmullq zmm30, \high, zmm24",
    r"vpaddq \low0, \low0, zmm30",
    r"vpmullq zmm30, \high, zmm25",
    r"vpaddq \low1, \low1, zmm30",
    r"vpmullq zmm30, \high, zmm26",
    r"vpaddq \low2, \low2, zmm30",
    r"vpmullq zmm30, \high, zmm27",
    r"vpsubq \low3, \low3, zmm30",
    r"vpmullq zmm30, \high, zmm28",
    r"vpaddq \low4, \low4, zmm30",
    r"vpmullq zmm30, \high, zmm29",
    r"vpsubq \low5, \low5, zmm30",
    r"vpxorq \high, \high, \high",
]

CARRY_ROUNDED_MACRO = [
    r"vpaddq zmm30, \limb, zmm31",
    "vpsraq zmm30, zmm30, 21",
    r"vpaddq \next, \next, zmm30",
    "vpsllq zmm30, zmm30, 21",
    r"vpsubq \limb, \limb, zmm30",
]

CARRY_MACRO = [
    r"vpsraq zmm30, \limb, 21",
    r"vpaddq \next, \next, zmm30",
    "vpsllq zmm30, zmm30, 21",
    r"vpsubq \limb, \limb, zmm30",
]


def expected_loads() -> list[str]:
    return [
        re.sub(r"\s+", " ", f"vmovdqu64 zmm{i}, ZMMWORD PTR [rdi + {64 * i:4d}]")
        for i in range(24)
    ]


EXPECTED_BROADCASTS = [
    f"vpbroadcastq zmm{24 + index}, QWORD PTR [rip + .Lscalar_{constant}]"
    for index, constant in enumerate(FOLD_CONSTANTS)
] + ["vpbroadcastq zmm31, QWORD PTR [rip + .Lscalar_round]"]


def expected_stores() -> list[str]:
    return [
        re.sub(r"\s+", " ", f"vmovdqu64 ZMMWORD PTR [rdi + {64 * i:3d}], zmm{i}")
        for i in range(12)
    ] + ["vzeroupper", "ret"]


# Pin every macro argument and the load point of the centered-carry constant.
# This is a semantic obligation, not merely a range-safety preference:
# FOLD low0 must equal high-12, and every carry must target limb+1. Keeping the
# transcript literal makes register-route review and mutation testing direct.
EXPECTED_REDUCTION_SCHEDULE = [
    "FOLD zmm23, zmm11, zmm12, zmm13, zmm14, zmm15, zmm16",
    "FOLD zmm22, zmm10, zmm11, zmm12, zmm13, zmm14, zmm15",
    "FOLD zmm21, zmm9, zmm10, zmm11, zmm12, zmm13, zmm14",
    "FOLD zmm20, zmm8, zmm9, zmm10, zmm11, zmm12, zmm13",
    "FOLD zmm19, zmm7, zmm8, zmm9, zmm10, zmm11, zmm12",
    "FOLD zmm18, zmm6, zmm7, zmm8, zmm9, zmm10, zmm11",
    "vpbroadcastq zmm31, QWORD PTR [rip + .Lscalar_round]",
    "CARRY_ROUNDED zmm6, zmm7",
    "CARRY_ROUNDED zmm8, zmm9",
    "CARRY_ROUNDED zmm10, zmm11",
    "CARRY_ROUNDED zmm12, zmm13",
    "CARRY_ROUNDED zmm14, zmm15",
    "CARRY_ROUNDED zmm16, zmm17",
    "CARRY_ROUNDED zmm7, zmm8",
    "CARRY_ROUNDED zmm9, zmm10",
    "CARRY_ROUNDED zmm11, zmm12",
    "CARRY_ROUNDED zmm13, zmm14",
    "CARRY_ROUNDED zmm15, zmm16",
    "FOLD zmm17, zmm5, zmm6, zmm7, zmm8, zmm9, zmm10",
    "FOLD zmm16, zmm4, zmm5, zmm6, zmm7, zmm8, zmm9",
    "FOLD zmm15, zmm3, zmm4, zmm5, zmm6, zmm7, zmm8",
    "FOLD zmm14, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7",
    "FOLD zmm13, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6",
    "FOLD zmm12, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5",
    "CARRY_ROUNDED zmm0, zmm1",
    "CARRY_ROUNDED zmm2, zmm3",
    "CARRY_ROUNDED zmm4, zmm5",
    "CARRY_ROUNDED zmm6, zmm7",
    "CARRY_ROUNDED zmm8, zmm9",
    "CARRY_ROUNDED zmm10, zmm11",
    "CARRY_ROUNDED zmm1, zmm2",
    "CARRY_ROUNDED zmm3, zmm4",
    "CARRY_ROUNDED zmm5, zmm6",
    "CARRY_ROUNDED zmm7, zmm8",
    "CARRY_ROUNDED zmm9, zmm10",
    "CARRY_ROUNDED zmm11, zmm12",
    "FOLD zmm12, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5",
    "CARRY zmm0, zmm1",
    "CARRY zmm1, zmm2",
    "CARRY zmm2, zmm3",
    "CARRY zmm3, zmm4",
    "CARRY zmm4, zmm5",
    "CARRY zmm5, zmm6",
    "CARRY zmm6, zmm7",
    "CARRY zmm7, zmm8",
    "CARRY zmm8, zmm9",
    "CARRY zmm9, zmm10",
    "CARRY zmm10, zmm11",
    "CARRY zmm11, zmm12",
    "FOLD zmm12, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5",
    "CARRY zmm0, zmm1",
    "CARRY zmm1, zmm2",
    "CARRY zmm2, zmm3",
    "CARRY zmm3, zmm4",
    "CARRY zmm4, zmm5",
    "CARRY zmm5, zmm6",
    "CARRY zmm6, zmm7",
    "CARRY zmm7, zmm8",
    "CARRY zmm8, zmm9",
    "CARRY zmm9, zmm10",
    "CARRY zmm10, zmm11",
]


def parse_arguments(line: str, name: str) -> list[str]:
    return [part.strip() for part in line.removeprefix(name + " ").split(",")]


class Certificate:
    def __init__(self, source_sha256: str) -> None:
        self.source_sha256 = source_sha256
        self.registers = {
            f"zmm{index}": Interval(0, B - 1 if index < 23 else (1 << 29) - 1)
            for index in range(24)
        }
        self.steps: list[dict[str, Any]] = []
        self.max_magnitude = 0
        self.max_label = ""
        self.fold_count = 0
        self.first_final_fold_checkpoint: dict[str, Interval] | None = None

    def record(self, operation: str, register: str, interval: Interval, rule: str) -> None:
        if interval.lower < I64_MIN or interval.upper > I64_MAX:
            raise AssertionError(
                f"signed int64 overflow at {operation}: "
                f"[{interval.lower}, {interval.upper}]"
            )
        magnitude = max(abs(interval.lower), abs(interval.upper))
        if magnitude > self.max_magnitude:
            self.max_magnitude = magnitude
            self.max_label = operation
        self.steps.append(
            {
                "index": len(self.steps),
                "operation": operation,
                "register": register,
                "lower": interval.lower,
                "upper": interval.upper,
                "rule": rule,
            }
        )

    def fold(self, arguments: list[str]) -> None:
        if len(arguments) != 7:
            raise AssertionError(f"FOLD expects 7 arguments: {arguments!r}")
        high, *low = arguments
        high_interval = self.registers[high]
        for target, constant, sign in zip(low, FOLD_CONSTANTS, FOLD_SIGNS):
            product = high_interval.multiply_constant(constant)
            self.record(
                f"vpmullq {high} * {constant}",
                "zmm30",
                product,
                "constant product interval; exact low-qword iff signed int64 bound holds",
            )
            if sign > 0:
                updated = self.registers[target].add(product)
                mnemonic = "vpaddq"
            else:
                updated = self.registers[target].subtract(product)
                mnemonic = "vpsubq"
            self.registers[target] = updated
            self.record(
                f"{mnemonic} {target}, {high}*{constant}",
                target,
                updated,
                "independent interval add/subtract",
            )
        self.registers[high] = Interval(0, 0)
        self.record(f"vpxorq {high}, {high}", high, Interval(0, 0), "xor self")
        self.fold_count += 1
        if self.fold_count == 13:
            self.first_final_fold_checkpoint = {
                f"zmm{index}": self.registers[f"zmm{index}"]
                for index in range(12)
            }

    def carry(self, arguments: list[str], rounded: bool) -> None:
        if len(arguments) != 2:
            raise AssertionError(f"CARRY expects 2 arguments: {arguments!r}")
        limb, following = arguments
        original = self.registers[limb]
        if rounded:
            biased = original.add(Interval(ROUND, ROUND))
            self.record(
                f"vpaddq {limb}, {ROUND}",
                "zmm30",
                biased,
                "interval plus centered-carry bias",
            )
            quotient = biased.floor_divide(B)
            residual = Interval(-ROUND, ROUND - 1)
        else:
            quotient = original.floor_divide(B)
            residual = Interval(0, B - 1)

        self.record(
            f"vpsraq floor({limb}/{B})" if not rounded else f"vpsraq floor(({limb}+{ROUND})/{B})",
            "zmm30",
            quotient,
            "arithmetic right shift equals floor division for signed int64",
        )
        next_interval = self.registers[following].add(quotient)
        self.registers[following] = next_interval
        self.record(
            f"vpaddq {following}, carry({limb})",
            following,
            next_interval,
            "independent interval addition",
        )
        reconstructed = quotient.multiply_constant(B)
        self.record(
            f"vpsllq carry({limb}), 21",
            "zmm30",
            reconstructed,
            "exact multiplication by 2^21 under signed int64 bound",
        )

        # q is derived from the same x, so treating x and q as independent
        # intervals would lose the defining floor relation. Euclidean division
        # gives this exact residual range for every integer x.
        self.registers[limb] = residual
        self.record(
            f"vpsubq {limb}, carry({limb})*{B}",
            limb,
            residual,
            "floor-division residual theorem (relational transfer)",
        )

    def result(self, call_count: int) -> dict[str, Any]:
        final = {
            register: {"lower": value.lower, "upper": value.upper}
            for register, value in sorted(
                self.registers.items(), key=lambda item: int(item[0][3:])
            )
        }
        for index in range(11):
            value = self.registers[f"zmm{index}"]
            if value.lower < 0 or value.upper >= B:
                raise AssertionError(f"unexpected final ordinary limb {index}: {value}")
        if self.registers["zmm12"] != Interval(0, 0):
            raise AssertionError(f"position 12 is not cleared: {self.registers['zmm12']}")

        if self.fold_count != 14 or self.first_final_fold_checkpoint is None:
            raise AssertionError("first-final-fold checkpoint was not reached exactly once")
        checkpoint = self.first_final_fold_checkpoint
        weighted_lower = sum(
            checkpoint[f"zmm{index}"].lower * B**index for index in range(12)
        )
        weighted_upper = sum(
            checkpoint[f"zmm{index}"].upper * B**index for index in range(12)
        )
        radix_12 = B**12
        if not (-radix_12 < weighted_lower <= weighted_upper < radix_12):
            raise AssertionError(
                "first-final-fold value escaped the one-window canonicality bound: "
                f"[{weighted_lower}, {weighted_upper}]"
            )
        return {
            "schema": "narya.scalar-reduce-source-bounds.v2",
            "source": "src/scalar_reduce_x8.S",
            "source_sha256": self.source_sha256,
            "radix": B,
            "signed_word_range": [I64_MIN, I64_MAX],
            "initial_bounds": {
                "limbs_0_through_22": [0, B - 1],
                "limb_23": [0, (1 << 29) - 1],
            },
            "fold_constants": list(FOLD_CONSTANTS),
            "fold_signs": list(FOLD_SIGNS),
            "fold_identity_exact": True,
            "macro_calls": call_count,
            "checked_machine_intermediates": len(self.steps),
            "maximum_absolute_intermediate": self.max_magnitude,
            "maximum_intermediate_operation": self.max_label,
            "maximum_intermediate_bits": self.max_magnitude.bit_length(),
            "first_final_fold_checkpoint": {
                "limbs": {
                    register: {"lower": value.lower, "upper": value.upper}
                    for register, value in checkpoint.items()
                },
                "weighted_lower": weighted_lower,
                "weighted_upper": weighted_upper,
                "strictly_inside_signed_radix_12_window": True,
            },
            "final_intervals": final,
            "claims": {
                "signed_no_wrap": True,
                "folds_preserve_mod_l": True,
                "carries_preserve_integer": True,
                "canonical_tail_checkpoint_bound": True,
                "canonical_output_range": False,
                "canonical_output_note":
                    "this checker establishes the pinned one-window hypothesis; "
                    "the separate Lean theorem closes the canonical tail, while "
                    "C packing remains separate",
                "parser_refinement": False,
                "packer_refinement": False,
                "assembled_instruction_refinement": False,
            },
            "steps": self.steps,
        }


def verify_constants(text: str) -> None:
    for constant in FOLD_CONSTANTS:
        pattern = rf"^\.Lscalar_{constant}: \.quad {constant}$"
        if re.search(pattern, text, re.MULTILINE) is None:
            raise AssertionError(f"missing or changed fold constant {constant}")
    if re.search(r"^\.Lscalar_round:\s+\.quad 1048576$", text, re.MULTILINE) is None:
        raise AssertionError("missing or changed centered-carry bias")

    c = L - (1 << 252)
    folded = sum(
        sign * constant * (B ** position)
        for position, (constant, sign) in enumerate(zip(FOLD_CONSTANTS, FOLD_SIGNS))
    )
    if folded != -c:
        raise AssertionError(f"fold identity failed: {folded} != {-c}")


def build_certificate() -> dict[str, Any]:
    source_bytes = SOURCE.read_bytes()
    text = source_bytes.decode("ascii")
    if macro_body(text, "FOLD") != FOLD_MACRO:
        raise AssertionError("FOLD macro differs from the certified instruction template")
    if macro_body(text, "CARRY_ROUNDED") != CARRY_ROUNDED_MACRO:
        raise AssertionError("CARRY_ROUNDED macro differs from the certified instruction template")
    if macro_body(text, "CARRY") != CARRY_MACRO:
        raise AssertionError("CARRY macro differs from the certified instruction template")
    verify_constants(text)

    body = function_body(text, "narya_scalar_reduce_radix21_x8_asm")
    loads = expected_loads()
    broadcasts = EXPECTED_BROADCASTS
    stores = expected_stores()
    if body[: len(loads)] != loads:
        raise AssertionError("radix-limb load map changed")
    if body[len(loads) : len(loads) + 6] != broadcasts[:6]:
        raise AssertionError("fold-constant broadcast map changed")
    if body[-len(stores) :] != stores:
        raise AssertionError("canonical-limb store map changed")

    schedule = body[len(loads) + 6 : -len(stores)]
    if schedule != EXPECTED_REDUCTION_SCHEDULE:
        raise AssertionError(
            "scalar reduction macro call order/register map or round broadcast changed"
        )
    certificate = Certificate(hashlib.sha256(source_bytes).hexdigest())
    call_count = 0
    for line in schedule:
        if line == broadcasts[6]:
            continue
        if line.startswith("FOLD "):
            certificate.fold(parse_arguments(line, "FOLD"))
        elif line.startswith("CARRY_ROUNDED "):
            certificate.carry(parse_arguments(line, "CARRY_ROUNDED"), True)
        elif line.startswith("CARRY "):
            certificate.carry(parse_arguments(line, "CARRY"), False)
        else:
            raise AssertionError(f"unsupported instruction in reduction schedule: {line}")
        call_count += 1
    return certificate.result(call_count)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json", action="store_true", help="emit every per-instruction interval as JSON"
    )
    arguments = parser.parse_args()
    certificate = build_certificate()
    if arguments.json:
        print(json.dumps(certificate, indent=2, sort_keys=True))
        return
    print(
        "OK: scalar reducer source has "
        f"{certificate['checked_machine_intermediates']} signed-safe intermediates"
    )
    print(
        "OK: largest absolute intermediate is "
        f"{certificate['maximum_absolute_intermediate']} "
        f"({certificate['maximum_intermediate_bits']} bits) at "
        f"{certificate['maximum_intermediate_operation']}"
    )
    print("OK: every position-pinned fold/carry preserves the scalar modulo l")
    print("OK: first-final-fold value lies strictly inside (-2^252, 2^252)")
    print("OPEN: C parser/packer and assembled-instruction refinement remain separate")


if __name__ == "__main__":
    main()
