#!/usr/bin/env python3
"""Extract the canonical linked r51 multiplier bytes into Lean.

The parser intentionally accepts only a little-endian ELF64 x86-64 image with
an ordinary section table and SYMTAB. It locates the exact multiplier and four
local constants by symbol, verifies their section permissions and extents,
and emits bytes from the final linked image. This binds a future Lean decoder
to an artifact, but is not itself an x86 decoder or a verified ELF parser.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import struct
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, Optional


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ELF = ROOT / "build/proof/r51x8_ifma.so"
GENERATED = ROOT / "formal/lean/NaryaFormal/GeneratedR51ObjectBytes.lean"

ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
SECTION_HEADER = struct.Struct("<IIQQQQIIQQ")
SYMBOL = struct.Struct("<IBBHQQ")

ELFCLASS64 = 2
ELFDATA2LSB = 1
ET_REL = 1
ET_DYN = 3
EM_X86_64 = 62
SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
STT_FUNC = 2


def fail(message: str) -> NoReturn:
    raise SystemExit(f"ELF object extraction failed: {message}")


@dataclass(frozen=True)
class Section:
    index: int
    name: str
    kind: int
    flags: int
    address: int
    offset: int
    size: int
    link: int
    info: int
    entry_size: int


@dataclass(frozen=True)
class Symbol:
    name: str
    info: int
    section_index: int
    value: int
    size: int


def cstring(data: bytes, offset: int) -> str:
    if offset < 0 or offset >= len(data):
        fail(f"string-table offset {offset} is out of range")
    end = data.find(b"\0", offset)
    if end < 0:
        fail(f"unterminated string at offset {offset}")
    try:
        return data[offset:end].decode("ascii")
    except UnicodeDecodeError as error:
        fail(f"non-ASCII ELF name at offset {offset}: {error}")


class Elf:
    def __init__(
        self, data: bytes, *, allowed_types: tuple[int, ...] = (ET_DYN,)
    ) -> None:
        self.data = data
        if len(data) < ELF_HEADER.size:
            fail("truncated ELF header")
        fields = ELF_HEADER.unpack_from(data)
        ident = fields[0]
        if ident[:4] != b"\x7fELF":
            fail("bad ELF magic")
        if ident[4] != ELFCLASS64 or ident[5] != ELFDATA2LSB or ident[6] != 1:
            fail("expected ELF64, little-endian, current-version image")
        elf_type, machine, version = fields[1], fields[2], fields[3]
        if elf_type not in allowed_types or machine != EM_X86_64 or version != 1:
            fail(
                f"expected x86-64 ELF type in {allowed_types}, got type={elf_type} "
                f"machine={machine} version={version}"
            )
        self.elf_type = elf_type
        section_offset = fields[6]
        section_entry_size = fields[11]
        section_count = fields[12]
        section_names_index = fields[13]
        if section_entry_size != SECTION_HEADER.size:
            fail(f"unexpected section-header size {section_entry_size}")
        if section_count == 0 or section_names_index >= section_count:
            fail("extended or invalid section table is unsupported")
        table_end = section_offset + section_count * section_entry_size
        if table_end > len(data):
            fail("section table extends beyond image")

        raw_sections = [
            SECTION_HEADER.unpack_from(data, section_offset + i * section_entry_size)
            for i in range(section_count)
        ]
        names_header = raw_sections[section_names_index]
        names = self.slice(names_header[4], names_header[5], "section-name table")
        self.sections = []
        for index, raw in enumerate(raw_sections):
            self.sections.append(
                Section(
                    index=index,
                    name=cstring(names, raw[0]),
                    kind=raw[1],
                    flags=raw[2],
                    address=raw[3],
                    offset=raw[4],
                    size=raw[5],
                    link=raw[6],
                    info=raw[7],
                    entry_size=raw[9],
                )
            )
        self.symbols = self.parse_symbols()

    def slice(self, offset: int, size: int, label: str) -> bytes:
        end = offset + size
        if offset < 0 or size < 0 or end > len(self.data):
            fail(f"{label} extends beyond image")
        return self.data[offset:end]

    def parse_symbols(self) -> dict[str, Symbol]:
        tables = [section for section in self.sections if section.kind == SHT_SYMTAB]
        if len(tables) != 1:
            fail(f"expected exactly one SYMTAB, found {len(tables)}")
        table = tables[0]
        if table.entry_size != SYMBOL.size or table.size % SYMBOL.size != 0:
            fail("unexpected symbol-table entry shape")
        if table.link >= len(self.sections):
            fail("symbol string-table link is invalid")
        strings_section = self.sections[table.link]
        strings = self.slice(strings_section.offset, strings_section.size, "string table")
        result: dict[str, Symbol] = {}
        for offset in range(table.offset, table.offset + table.size, SYMBOL.size):
            name_offset, info, _other, section_index, value, size = SYMBOL.unpack_from(
                self.data, offset
            )
            name = cstring(strings, name_offset)
            if not name:
                continue
            if name in result:
                fail(f"duplicate symbol {name!r}")
            result[name] = Symbol(name, info, section_index, value, size)
        return result

    def symbol_bytes(
        self,
        name: str,
        *,
        expected_size: Optional[int],
        executable: bool,
    ) -> tuple[Symbol, bytes]:
        symbol = self.symbols.get(name)
        if symbol is None:
            fail(f"missing symbol {name}")
        if symbol.section_index == 0 or symbol.section_index >= len(self.sections):
            fail(f"symbol {name} has invalid section {symbol.section_index}")
        section = self.sections[symbol.section_index]
        if section.kind != SHT_PROGBITS or not (section.flags & SHF_ALLOC):
            fail(f"symbol {name} is not in allocated PROGBITS")
        if bool(section.flags & SHF_EXECINSTR) != executable:
            fail(f"symbol {name} executable-section property changed")
        if not executable and section.flags & SHF_WRITE:
            fail(f"constant symbol {name} moved into writable memory")
        size = symbol.size if expected_size is None else expected_size
        if expected_size is not None and symbol.size not in (0, expected_size):
            fail(f"symbol {name} reports size {symbol.size}, expected {expected_size}")
        relative = symbol.value - section.address
        if relative < 0 or relative + size > section.size:
            fail(f"symbol {name} extends beyond section {section.name}")
        return symbol, self.slice(section.offset + relative, size, name)


def nat_list(data: bytes, indent: str = "  ") -> str:
    rows = []
    for start in range(0, len(data), 16):
        row = ", ".join(str(value) for value in data[start : start + 16])
        rows.append(indent + row)
    return "[\n" + ",\n".join(rows) + "\n]"


def render(data: bytes) -> str:
    elf = Elf(data)
    function, code = elf.symbol_bytes(
        "narya_r51x8_mul_ifma", expected_size=None, executable=True
    )
    if (function.info & 0xF) != STT_FUNC or function.size == 0:
        fail("multiplier is not a nonempty STT_FUNC symbol")

    constants: list[tuple[str, Symbol, bytes]] = []
    for name in (
        "narya_ifma_mask51",
        "narya_ifma_fold19",
        "narya_ifma_sub_bias0",
        "narya_ifma_sub_biasn",
    ):
        symbol, value = elf.symbol_bytes(
            name, expected_size=8, executable=False
        )
        constants.append((name, symbol, value))

    expected_values = {
        "narya_ifma_mask51": (1 << 51) - 1,
        "narya_ifma_fold19": 19,
        "narya_ifma_sub_bias0": 4 * ((1 << 51) - 19),
        "narya_ifma_sub_biasn": 4 * ((1 << 51) - 1),
    }
    for name, _symbol, value in constants:
        actual = int.from_bytes(value, "little")
        if actual != expected_values[name]:
            fail(f"constant {name} is {actual}, expected {expected_values[name]}")

    code_sha256 = hashlib.sha256(code).hexdigest()
    elf_sha256 = hashlib.sha256(data).hexdigest()
    constant_definitions = "\n".join(
        f"def {name.removeprefix('narya_')}Address : Nat := {symbol.value}\n"
        f"def {name.removeprefix('narya_')}Bytes : List Nat := {nat_list(value)}"
        for name, symbol, value in constants
    )
    return f"""/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Generated by tools/generate_r51_object_bytes.py from the canonical linked ELF.
Do not edit by hand. These are exact final symbol and constant bytes, not a
decoded instruction list and not an x86 execution proof.

Canonical ELF SHA-256: {elf_sha256}
Multiplier bytes SHA-256: {code_sha256}
-/

namespace NaryaFormal.R51Object

def symbolAddress : Nat := {function.value}
def symbolSize : Nat := {function.size}
def symbolBytes : List Nat := {nat_list(code)}

{constant_definitions}

end NaryaFormal.R51Object
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--elf", type=Path, default=DEFAULT_ELF)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()

    generated = render(arguments.elf.read_bytes())
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
                    tofile=f"generated from {arguments.elf}",
                )
            )
            fail("linked object bytes differ from the committed Lean artifact")
        print("OK: canonical linked multiplier bytes match committed Lean input")
        return
    sys.stdout.write(generated)


if __name__ == "__main__":
    main()
