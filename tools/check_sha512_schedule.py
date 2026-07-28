#!/usr/bin/env python3
"""Certify the source schedule of src/sha512x8.S against SHA-512.

This is a fail-closed source checker, not an ELF decoder. It validates the
literal round constants, exact macro instruction templates, ternary-logic
truth tables, all 80 rolling working-state maps, all 64 rolling message-ring
updates, and the load/feed-forward/store map.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/sha512x8.S"

FIPS_K = (
    0x428A2F98D728AE22, 0x7137449123EF65CD, 0xB5C0FBCFEC4D3B2F,
    0xE9B5DBA58189DBBC, 0x3956C25BF348B538, 0x59F111F1B605D019,
    0x923F82A4AF194F9B, 0xAB1C5ED5DA6D8118, 0xD807AA98A3030242,
    0x12835B0145706FBE, 0x243185BE4EE4B28C, 0x550C7DC3D5FFB4E2,
    0x72BE5D74F27B896F, 0x80DEB1FE3B1696B1, 0x9BDC06A725C71235,
    0xC19BF174CF692694, 0xE49B69C19EF14AD2, 0xEFBE4786384F25E3,
    0x0FC19DC68B8CD5B5, 0x240CA1CC77AC9C65, 0x2DE92C6F592B0275,
    0x4A7484AA6EA6E483, 0x5CB0A9DCBD41FBD4, 0x76F988DA831153B5,
    0x983E5152EE66DFAB, 0xA831C66D2DB43210, 0xB00327C898FB213F,
    0xBF597FC7BEEF0EE4, 0xC6E00BF33DA88FC2, 0xD5A79147930AA725,
    0x06CA6351E003826F, 0x142929670A0E6E70, 0x27B70A8546D22FFC,
    0x2E1B21385C26C926, 0x4D2C6DFC5AC42AED, 0x53380D139D95B3DF,
    0x650A73548Baf63DE, 0x766A0ABB3C77B2A8, 0x81C2C92E47EDAEE6,
    0x92722C851482353B, 0xA2BFE8A14CF10364, 0xA81A664BBC423001,
    0xC24B8B70D0F89791, 0xC76C51A30654BE30, 0xD192E819D6EF5218,
    0xD69906245565A910, 0xF40E35855771202A, 0x106AA07032BBD1B8,
    0x19A4C116B8D2D0C8, 0x1E376C085141AB53, 0x2748774CDF8EEB99,
    0x34B0BCB5E19B48A8, 0x391C0CB3C5C95A63, 0x4ED8AA4AE3418ACB,
    0x5B9CCA4F7763E373, 0x682E6FF3D6B2B8A3, 0x748F82EE5DEFB2FC,
    0x78A5636F43172F60, 0x84C87814A1F0AB72, 0x8CC702081A6439EC,
    0x90BEFFFA23631E28, 0xA4506CEBDE82BDE9, 0xBEF9A3F7B2C67915,
    0xC67178F2E372532B, 0xCA273ECEEA26619C, 0xD186B8C721C0C207,
    0xEADA7DD6CDE0EB1E, 0xF57D4F7FEE6ED178, 0x06F067AA72176FBA,
    0x0A637DC5A2C898A6, 0x113F9804BEF90DAE, 0x1B710B35131C471B,
    0x28DB77F523047D84, 0x32CAAB7B40C72493, 0x3C9EBE0A15C9BEBC,
    0x431D67C49C100D4C, 0x4CC5D4BECb3E42B6, 0x597F299CFC657E2A,
    0x5FCB6FAB3AD6FAEC, 0x6C44198C4A475817,
)


def strip_comments(text: str) -> str:
    return re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)


def normalized_lines(text: str) -> list[str]:
    return [re.sub(r"\s+", " ", line.strip()) for line in text.splitlines() if line.strip()]


def macro_body(text: str, name: str) -> list[str]:
    clean = strip_comments(text)
    match = re.search(
        rf"^\.macro {re.escape(name)}(?:[ \t]+[^\n]*)?\n(?P<body>.*?)^\.endm$",
        clean,
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


ROUND_MACRO = [
    r"vprorq zmm8, \E, 14",
    r"vprorq zmm9, \E, 18",
    "vpxorq zmm8, zmm8, zmm9",
    r"vprorq zmm9, \E, 41",
    "vpxorq zmm8, zmm8, zmm9",
    r"vmovdqa64 zmm10, \E",
    r"vpternlogq zmm10, \F, \G, 0xca",
    r"vpaddq zmm8, zmm8, \H",
    "vpaddq zmm8, zmm8, zmm10",
    r"vpbroadcastq zmm15, QWORD PTR [rdx + \KOFF]",
    "vpaddq zmm8, zmm8, zmm15",
    r"vpaddq zmm8, zmm8, \W",
    r"vprorq zmm9, \A, 28",
    r"vprorq zmm11, \A, 34",
    "vpxorq zmm9, zmm9, zmm11",
    r"vprorq zmm11, \A, 39",
    "vpxorq zmm9, zmm9, zmm11",
    r"vmovdqa64 zmm10, \A",
    r"vpternlogq zmm10, \B, \C, 0xe8",
    "vpaddq zmm9, zmm9, zmm10",
    r"vpaddq \D, \D, zmm8",
    r"vpaddq \H, zmm8, zmm9",
]

EXPAND_MACRO = [
    r"vprorq zmm12, \W1, 1",
    r"vprorq zmm13, \W1, 8",
    r"vpsrlq zmm14, \W1, 7",
    "vpternlogq zmm12, zmm13, zmm14, 0x96",
    r"vprorq zmm13, \W14, 19",
    r"vprorq zmm14, \W14, 61",
    r"vpsrlq zmm15, \W14, 6",
    "vpternlogq zmm13, zmm14, zmm15, 0x96",
    r"vpaddq \W0, \W0, zmm12",
    r"vpaddq \W0, \W0, \W9",
    r"vpaddq \W0, \W0, zmm13",
]


def ternary_immediate(function) -> int:
    immediate = 0
    for destination in (0, 1):
        for source1 in (0, 1):
            for source2 in (0, 1):
                # Intel's truth-table index is DEST:SRC1:SRC2.
                index = (destination << 2) | (source1 << 1) | source2
                immediate |= function(destination, source1, source2) << index
    return immediate


def verify_truth_tables() -> None:
    choose = ternary_immediate(lambda e, f, g: (e & f) ^ ((1 - e) & g))
    majority = ternary_immediate(lambda a, b, c: (a & b) ^ (a & c) ^ (b & c))
    three_xor = ternary_immediate(lambda a, b, c: a ^ b ^ c)
    if (choose, majority, three_xor) != (0xCA, 0xE8, 0x96):
        raise AssertionError(
            f"ternary truth-table mismatch: {(choose, majority, three_xor)!r}"
        )


def verify_constants(text: str) -> None:
    match = re.search(
        r"^narya_sha512_round_constants:\n(?P<body>.*?)^\.section \.note\.GNU-stack",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise AssertionError("missing SHA-512 round-constant table")
    constants = tuple(
        int(value, 16)
        for value in re.findall(r"^\s*\.quad\s+(0x[0-9a-fA-F]+)\s*$", match.group("body"), re.MULTILINE)
    )
    if constants != FIPS_K:
        for index, expected in enumerate(FIPS_K):
            actual = constants[index] if index < len(constants) else None
            if actual != expected:
                raise AssertionError(
                    f"SHA-512 K[{index}]={actual!r}, expected 0x{expected:016x}"
                )
        raise AssertionError(f"SHA-512 constant count {len(constants)}, expected 80")


def expected_prefix() -> list[str]:
    block_loads = [
        re.sub(r"\s+", " ", f"vmovdqu64 zmm{16 + i}, ZMMWORD PTR [rsi + {64 * i:3d}]")
        for i in range(16)
    ]
    state_loads = [
        re.sub(r"\s+", " ", f"vmovdqu64 zmm{i}, ZMMWORD PTR [rdi + {64 * i:3d}]")
        for i in range(8)
    ]
    return [*block_loads, *state_loads, "lea rdx, [rip + narya_sha512_round_constants]"]


def expected_suffix() -> list[str]:
    feed_forward = [
        re.sub(r"\s+", " ", f"vpaddq zmm{i}, zmm{i}, ZMMWORD PTR [rdi + {64 * i:3d}]")
        for i in range(8)
    ]
    stores = [
        re.sub(r"\s+", " ", f"vmovdqu64 ZMMWORD PTR [rdi + {64 * i:3d}], zmm{i}")
        for i in range(8)
    ]
    return [*feed_forward, *stores, "vzeroupper", "ret"]


def parse_call(line: str, name: str) -> list[str]:
    return [part.strip() for part in line.removeprefix(name + " ").split(",")]


def expected_working_registers(round_index: int) -> list[str]:
    return [f"zmm{(position - round_index) % 8}" for position in range(8)]


def verify_round_schedule(lines: list[str]) -> None:
    cursor = 0
    ring = {f"zmm{16 + index}": index for index in range(16)}

    for round_index in range(80):
        if round_index >= 16:
            if cursor >= len(lines) or not lines[cursor].startswith("SHA512_EXPAND "):
                raise AssertionError(f"round {round_index}: missing preceding SHA512_EXPAND")
            arguments = parse_call(lines[cursor], "SHA512_EXPAND")
            expected_registers = [
                f"zmm{16 + (round_index + offset) % 16}"
                for offset in (0, 1, 9, 14)
            ]
            if arguments != expected_registers:
                raise AssertionError(
                    f"round {round_index}: expand registers {arguments}, expected {expected_registers}"
                )
            represented = [ring[register] for register in arguments]
            expected_words = [round_index - 16, round_index - 15, round_index - 7, round_index - 2]
            if represented != expected_words:
                raise AssertionError(
                    f"round {round_index}: ring contains W{represented}, expected W{expected_words}"
                )
            ring[arguments[0]] = round_index
            cursor += 1

        if cursor >= len(lines) or not lines[cursor].startswith("SHA512_ROUND "):
            raise AssertionError(f"round {round_index}: missing SHA512_ROUND")
        arguments = parse_call(lines[cursor], "SHA512_ROUND")
        expected = [
            *expected_working_registers(round_index),
            f"zmm{16 + round_index % 16}",
            str(round_index * 8),
        ]
        if arguments != expected:
            raise AssertionError(
                f"round {round_index}: args {arguments}, expected {expected}"
            )
        if ring[arguments[8]] != round_index:
            raise AssertionError(
                f"round {round_index}: {arguments[8]} contains W{ring[arguments[8]]}"
            )
        cursor += 1

    if cursor != len(lines):
        raise AssertionError(f"unexpected schedule lines after round 79: {lines[cursor:]!r}")


def main() -> None:
    text = SOURCE.read_text(encoding="ascii")
    verify_constants(text)
    verify_truth_tables()
    if macro_body(text, "SHA512_ROUND") != ROUND_MACRO:
        raise AssertionError("SHA512_ROUND differs from certified FIPS operation template")
    if macro_body(text, "SHA512_EXPAND") != EXPAND_MACRO:
        raise AssertionError("SHA512_EXPAND differs from certified FIPS recurrence template")

    body = function_body(text, "narya_sha512_compress_x8_asm")
    prefix = expected_prefix()
    suffix = expected_suffix()
    if body[: len(prefix)] != prefix:
        raise AssertionError("SHA-512 block/state load map changed")
    if body[-len(suffix) :] != suffix:
        raise AssertionError("SHA-512 feed-forward/store map changed")
    verify_round_schedule(body[len(prefix) : -len(suffix)])

    print("OK: all 80 SHA-512 constants match FIPS 180-4")
    print("OK: sigma rotations and Ch/Maj/XOR truth tables match SHA-512")
    print("OK: all 80 working-state maps and 64 rolling-ring expansions are exact")
    print("OK: block/state loads and Davies-Meyer feed-forward stores preserve word/lane order")


if __name__ == "__main__":
    main()
