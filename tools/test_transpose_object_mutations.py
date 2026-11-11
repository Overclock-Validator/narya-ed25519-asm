#!/usr/bin/env python3
"""Require the exact-object transpose checker to fail closed on byte mutations."""
from __future__ import annotations

import struct
import tempfile
from dataclasses import dataclass
from pathlib import Path

import check_transpose_object_trace as checker

ROOT = Path(__file__).resolve().parents[1]
PROJECTIVE = ROOT / "build/proof/projective_niels_transpose_x8.o"
AFFINE = ROOT / "build/proof/affine_niels_transpose_x8.o"


@dataclass(frozen=True)
class Mutation:
    name: str
    object_path: Path
    symbol: str
    anchor: bytes
    replacement: bytes
    occurrence: int = 0


MUTATIONS = (
    Mutation(
        "projective-pointer-assignment",
        PROJECTIVE,
        checker.PROJECTIVE_SYMBOL,
        bytes.fromhex("488b16"),
        bytes.fromhex("488b0e"),
    ),
    Mutation(
        "projective-pointer-table-offset",
        PROJECTIVE,
        checker.PROJECTIVE_SYMBOL,
        bytes.fromhex("488b4e08"),
        bytes.fromhex("488b4e10"),
    ),
    Mutation(
        "projective-source-load-offset",
        PROJECTIVE,
        checker.PROJECTIVE_SYMBOL,
        bytes.fromhex("c5fe6f8280000000"),
        bytes.fromhex("c5fe6f8260000000"),
    ),
    Mutation(
        "projective-output-store-offset",
        PROJECTIVE,
        checker.PROJECTIVE_SYMBOL,
        bytes.fromhex("c5fe7f98e0040000"),
        bytes.fromhex("c5fe7f98d8040000"),
    ),
    Mutation(
        "projective-shuffle-immediate",
        PROJECTIVE,
        checker.PROJECTIVE_SYMBOL,
        bytes.fromhex("62f3dd2843d603"),
        bytes.fromhex("62f3dd2843d602"),
    ),
    Mutation(
        "projective-vzeroupper",
        PROJECTIVE,
        checker.PROJECTIVE_SYMBOL,
        bytes.fromhex("c5f877c3"),
        bytes.fromhex("c5f876c3"),
    ),
    Mutation(
        "affine-mask-immediate",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("b807000000"),
        bytes.fromhex("b80f000000"),
    ),
    Mutation(
        "affine-mask-register",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("c5f992c8"),
        bytes.fromhex("c5f992d0"),
    ),
    Mutation(
        "affine-load-zeroing-bit",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("62f1fea96f02"),
        bytes.fromhex("62f1fe296f02"),
    ),
    Mutation(
        "affine-load-mask-field",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("62f1fea96f02"),
        bytes.fromhex("62f1feaa6f02"),
    ),
    Mutation(
        "affine-guard-tail-load-offset",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("62f1fea96f4203"),
        bytes.fromhex("62f1fea96f4204"),
    ),
    Mutation(
        "affine-output-store-offset",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("c5fe7f90a0030000"),
        bytes.fromhex("c5fe7f9098030000"),
    ),
    Mutation(
        "affine-ret",
        AFFINE,
        checker.AFFINE_SYMBOL,
        bytes.fromhex("c5f877c3"),
        bytes.fromhex("c5f87790"),
    ),
)


def mutate(mutation: Mutation, destination: Path) -> None:
    data = bytearray(mutation.object_path.read_bytes())
    elf = checker.Elf(bytes(data))
    _symbol, start, end = elf.symbol_file_range(mutation.symbol)
    code = bytes(data[start:end])
    count = code.count(mutation.anchor)
    if count <= mutation.occurrence:
        raise SystemExit(
            f"{mutation.name}: anchor occurs {count} times, "
            f"cannot mutate occurrence {mutation.occurrence}"
        )
    offset = -1
    search_from = 0
    for _ in range(mutation.occurrence + 1):
        offset = code.index(mutation.anchor, search_from)
        search_from = offset + 1
    if len(mutation.anchor) != len(mutation.replacement):
        raise SystemExit(f"{mutation.name}: mutation must preserve symbol size")
    data[start + offset : start + offset + len(mutation.anchor)] = mutation.replacement
    destination.write_bytes(data)


def check_rejected(mutation: Mutation) -> None:
    with tempfile.TemporaryDirectory(prefix="narya-transpose-mutation-") as directory:
        mutated = Path(directory) / mutation.object_path.name
        mutate(mutation, mutated)
        try:
            if mutation.object_path == PROJECTIVE:
                checker.check_object(mutated, checker.PROJECTIVE_SYMBOL, checker.expected_projective(), False)
            else:
                checker.check_object(mutated, checker.AFFINE_SYMBOL, checker.expected_affine(), True)
        except checker.CheckError as error:
            print(f"OK: mutation {mutation.name} rejected: {error}")
            return
        raise SystemExit(f"mutation {mutation.name!r} was not detected")



def mutate_symbol_size(object_path: Path, symbol_name: str, destination: Path) -> None:
    data = bytearray(object_path.read_bytes())
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise SystemExit("symbol-size mutation expects ELF64 little-endian")
    shoff = struct.unpack_from("<Q", data, 40)[0]
    shentsize, shnum = struct.unpack_from("<HH", data, 58)[:2]
    if shentsize != 64:
        raise SystemExit("unexpected section-header size")
    for section_index in range(shnum):
        header = shoff + section_index * shentsize
        section_type = struct.unpack_from("<I", data, header + 4)[0]
        if section_type != checker.SHT_SYMTAB:
            continue
        section_offset = struct.unpack_from("<Q", data, header + 24)[0]
        section_size = struct.unpack_from("<Q", data, header + 32)[0]
        string_index = struct.unpack_from("<I", data, header + 40)[0]
        entry_size = struct.unpack_from("<Q", data, header + 56)[0] or 24
        string_header = shoff + string_index * shentsize
        string_offset = struct.unpack_from("<Q", data, string_header + 24)[0]
        string_size = struct.unpack_from("<Q", data, string_header + 32)[0]
        strings = bytes(data[string_offset : string_offset + string_size])
        for entry in range(section_offset, section_offset + section_size, entry_size):
            name_offset = struct.unpack_from("<I", data, entry)[0]
            end = strings.find(b"\0", name_offset)
            if end < 0:
                end = len(strings)
            name = strings[name_offset:end].decode("ascii") if name_offset < len(strings) else ""
            if name == symbol_name:
                size = struct.unpack_from("<Q", data, entry + 16)[0]
                if size < 2:
                    raise SystemExit("cannot shrink target symbol")
                struct.pack_into("<Q", data, entry + 16, size - 1)
                destination.write_bytes(data)
                return
    raise SystemExit(f"symbol {symbol_name!r} not found for size mutation")


def mutate_executable_relocation(object_path: Path, symbol_name: str, destination: Path) -> None:
    data = bytearray(object_path.read_bytes())
    elf = checker.Elf(bytes(data))
    symbol, _start, _end = elf.symbol_file_range(symbol_name)
    shoff = struct.unpack_from("<Q", data, 40)[0]
    shentsize = struct.unpack_from("<H", data, 58)[0]
    header = shoff + symbol.section_index * shentsize
    # Reclassify the nonempty executable section as a relocation section aimed
    # at itself.  The checker must reject the now-nonempty relocation input
    # before it attempts to trust the instruction transcript.
    struct.pack_into("<I", data, header + 4, checker.SHT_RELA)
    struct.pack_into("<I", data, header + 44, symbol.section_index)
    destination.write_bytes(data)


def check_special_rejected(name: str, object_path: Path, symbol: str, mutator) -> None:
    with tempfile.TemporaryDirectory(prefix="narya-transpose-special-mutation-") as directory:
        mutated = Path(directory) / object_path.name
        mutator(object_path, symbol, mutated)
        try:
            if object_path == PROJECTIVE:
                checker.check_object(mutated, checker.PROJECTIVE_SYMBOL, checker.expected_projective(), False)
            else:
                checker.check_object(mutated, checker.AFFINE_SYMBOL, checker.expected_affine(), True)
        except checker.CheckError as error:
            print(f"OK: mutation {name} rejected: {error}")
            return
        raise SystemExit(f"mutation {name!r} was not detected")


def main() -> None:
    checker.run(PROJECTIVE, AFFINE)
    for mutation in MUTATIONS:
        check_rejected(mutation)
    check_special_rejected(
        "projective-symbol-size", PROJECTIVE, checker.PROJECTIVE_SYMBOL, mutate_symbol_size
    )
    check_special_rejected(
        "affine-executable-relocation", AFFINE, checker.AFFINE_SYMBOL, mutate_executable_relocation
    )
    print(f"PASS: all {len(MUTATIONS) + 2} whole-leaf object mutations were rejected")


if __name__ == "__main__":
    main()
