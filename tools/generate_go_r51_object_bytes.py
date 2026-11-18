#!/usr/bin/env python3
"""Extract the Go-linked production r51 multiplier bytes into Lean.

The production verifier is the Go module `narya-ed25519`. Its x8 multiplier is
the Go assembly function `ifmaMulNormalizedUncheckedX8`, which the Go
toolchain assembles and links independently of this repository's GNU assembly
source. This tool reads a linked ELF64 x86-64 Go binary, locates the exact ABI0
symbol and its two read-only constants, and emits their final bytes as Lean
input for `X86GoR51MulReflective.lean`.

It is a byte extractor, not a decoder: the Lean kernel decodes and checks the
emitted bytes. It refuses any image in which the symbol is not in an
executable, non-writable section or a constant is not in read-only data.

Reference build (run inside a `narya-ed25519` checkout at the pinned commit):

    GOOS=linux GOARCH=amd64 GOTOOLCHAIN=<pinned> go test -c -trimpath \\
        -buildvcs=false -ldflags=-buildid= -o r51x5.test ./internal/r51x5
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import struct
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean/NaryaFormal"

PACKAGE = "github.com/Overclock-Validator/narya-ed25519/internal/r51x5"


@dataclass(frozen=True)
class Leaf:
    """One Go assembly leaf whose linked bytes are committed as Lean input."""

    function: str
    module: str
    namespace: str
    description: str
    constants: tuple[str, ...] = ("ifmaFold19", "ifmaLimbMask51")

    @property
    def symbol(self) -> str:
        return f"{PACKAGE}.{self.function}.abi0"

    @property
    def generated(self) -> Path:
        return LEAN / f"{self.module}.lean"


LEAVES = {
    "mul": Leaf(
        "ifmaMulNormalizedUncheckedX8",
        "GeneratedGoR51ObjectBytes",
        "NaryaFormal.GoR51Object",
        "multiplier",
    ),
    "normalize": Leaf(
        "ifmaNormalizeProductUncheckedX8",
        "GeneratedGoR51NormalizeObjectBytes",
        "NaryaFormal.GoR51NormalizeObject",
        "product normalizer",
    ),
    "add": Leaf(
        "ifmaAddNormalizedUncheckedX8",
        "GeneratedGoR51AddObjectBytes",
        "NaryaFormal.GoR51AddObject",
        "adder",
    ),
    "subtract": Leaf(
        "ifmaSubtractNormalizedUncheckedX8",
        "GeneratedGoR51SubtractObjectBytes",
        "NaryaFormal.GoR51SubtractObject",
        "subtractor",
        ("ifmaSubBias0", "ifmaSubBiasN", "ifmaFold19", "ifmaLimbMask51"),
    ),
    "negate": Leaf(
        "ifmaNegateNormalizedUncheckedX8",
        "GeneratedGoR51NegateObjectBytes",
        "NaryaFormal.GoR51NegateObject",
        "negator",
        ("ifmaSubBias0", "ifmaSubBiasN", "ifmaFold19", "ifmaLimbMask51"),
    ),
}

# Read-only qword constants and the values the proofs require of them.
CONSTANT_VALUES = {
    "ifmaFold19": 19,
    "ifmaLimbMask51": (1 << 51) - 1,
    "ifmaSubBias0": 4 * ((1 << 51) - 19),
    "ifmaSubBiasN": 4 * ((1 << 51) - 1),
}


def constant_symbol(name: str) -> str:
    return f"{PACKAGE}.{name}"
FOLD19 = f"{PACKAGE}.ifmaFold19"
MASK51 = f"{PACKAGE}.ifmaLimbMask51"

# Pinned provenance of the committed reference bytes. Changing either value is
# an explicit statement that the Lean proof was rebuilt for the new artifact.
PINNED_MODULE_COMMIT = "c265ee9667131a556cd332c252b79de0860c7640"
PINNED_GO_VERSION = "go1.27.3"

ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
SECTION_HEADER = struct.Struct("<IIQQQQIIQQ")
SYMBOL = struct.Struct("<IBBHQQ")

ET_EXEC = 2
ET_DYN = 3
EM_X86_64 = 62
SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
STT_FUNC = 2


def fail(message: str) -> NoReturn:
    raise SystemExit(f"Go ELF extraction failed: {message}")


@dataclass(frozen=True)
class Extracted:
    address: int
    data: bytes


class GoElf:
    """Minimal fail-closed ELF64 reader for named symbols."""

    def __init__(self, data: bytes) -> None:
        self.data = data
        if len(data) < ELF_HEADER.size:
            fail("truncated ELF header")
        fields = ELF_HEADER.unpack_from(data)
        ident = fields[0]
        if ident[:4] != b"\x7fELF" or ident[4] != 2 or ident[5] != 1:
            fail("expected a little-endian ELF64 image")
        if fields[1] not in (ET_EXEC, ET_DYN) or fields[2] != EM_X86_64:
            fail(f"expected a linked x86-64 image, got type={fields[1]} machine={fields[2]}")
        offset, entry_size, count = fields[6], fields[11], fields[12]
        if entry_size != SECTION_HEADER.size or count == 0:
            fail("unsupported section table")
        if offset + count * entry_size > len(data):
            fail("section table extends beyond image")
        self.sections = [
            SECTION_HEADER.unpack_from(data, offset + index * entry_size)
            for index in range(count)
        ]

    def slice(self, offset: int, size: int, label: str) -> bytes:
        if offset < 0 or size < 0 or offset + size > len(self.data):
            fail(f"{label} extends beyond image")
        return self.data[offset : offset + size]

    def find(self, wanted: set[str]) -> dict[str, tuple[int, int, int, int]]:
        tables = [section for section in self.sections if section[1] == SHT_SYMTAB]
        if len(tables) != 1:
            fail(f"expected exactly one SYMTAB, found {len(tables)}")
        table = tables[0]
        if table[9] != SYMBOL.size or table[5] % SYMBOL.size != 0:
            fail("unexpected symbol-table entry shape")
        if table[6] >= len(self.sections):
            fail("symbol string-table link is invalid")
        strings_header = self.sections[table[6]]
        strings = self.slice(strings_header[4], strings_header[5], "string table")
        encoded = {name.encode("ascii"): name for name in wanted}
        found: dict[str, tuple[int, int, int, int]] = {}
        for offset in range(table[4], table[4] + table[5], SYMBOL.size):
            name_offset, info, _other, section_index, value, size = SYMBOL.unpack_from(
                self.data, offset
            )
            end = strings.find(b"\0", name_offset)
            if end < 0:
                fail("unterminated symbol name")
            name = encoded.get(strings[name_offset:end])
            if name is None:
                continue
            if name in found:
                fail(f"duplicate symbol {name}")
            found[name] = (info, section_index, value, size)
        missing = wanted - set(found)
        if missing:
            fail(f"missing symbols: {sorted(missing)}")
        return found

    def symbol_bytes(
        self, entry: tuple[int, int, int, int], name: str, *, executable: bool
    ) -> Extracted:
        _info, section_index, value, size = entry
        if section_index == 0 or section_index >= len(self.sections):
            fail(f"symbol {name} has invalid section {section_index}")
        section = self.sections[section_index]
        kind, flags, address, offset, section_size = (
            section[1], section[2], section[3], section[4], section[5],
        )
        if kind != SHT_PROGBITS or not flags & SHF_ALLOC:
            fail(f"symbol {name} is not in allocated PROGBITS")
        if flags & SHF_WRITE:
            fail(f"symbol {name} is in writable memory")
        if bool(flags & SHF_EXECINSTR) != executable:
            fail(f"symbol {name} executable-section property is wrong")
        relative = value - address
        if size == 0 or relative < 0 or relative + size > section_size:
            fail(f"symbol {name} has an invalid extent")
        return Extracted(value, self.slice(offset + relative, size, name))


@dataclass(frozen=True)
class GoSymbol:
    function: Extracted
    constants: tuple[tuple[str, Extracted], ...]
    image_sha256: str


def extract(data: bytes, leaf: Leaf = LEAVES["mul"]) -> GoSymbol:
    elf = GoElf(data)
    names = {name: constant_symbol(name) for name in leaf.constants}
    entries = elf.find({leaf.symbol, *names.values()})
    if entries[leaf.symbol][0] & 0xF != STT_FUNC:
        fail(f"{leaf.function} is not an STT_FUNC symbol")
    function = elf.symbol_bytes(entries[leaf.symbol], leaf.symbol, executable=True)
    constants = []
    for name, symbol in names.items():
        value = elf.symbol_bytes(entries[symbol], symbol, executable=False)
        if len(value.data) != 8 or (
            int.from_bytes(value.data, "little") != CONSTANT_VALUES[name]
        ):
            fail(f"constant {name} is not the qword {CONSTANT_VALUES[name]}")
        constants.append((name, value))
    return GoSymbol(function, tuple(constants), hashlib.sha256(data).hexdigest())


def nat_list(data: bytes, indent: str = "  ") -> str:
    rows = []
    for start in range(0, len(data), 16):
        rows.append(indent + ", ".join(str(value) for value in data[start : start + 16]))
    return "[\n" + ",\n".join(rows) + "\n]"


def render(symbol: GoSymbol, leaf: Leaf = LEAVES["mul"]) -> str:
    code_sha256 = hashlib.sha256(symbol.function.data).hexdigest()
    constant_definitions = "\n".join(
        f"def {name}Address : Nat := {value.address}\n"
        f"def {name}Bytes : List Nat := {nat_list(value.data)}"
        for name, value in symbol.constants
    )
    return f"""/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Generated by tools/generate_go_r51_object_bytes.py from a linked Go binary.
Do not edit by hand. These are the exact final bytes of the production Go
assembly {leaf.description} and its constants, not a decoded instruction list and
not an execution proof.

Module: github.com/Overclock-Validator/narya-ed25519
Module commit: {PINNED_MODULE_COMMIT}
Toolchain: {PINNED_GO_VERSION}, GOOS=linux GOARCH=amd64
Build: go test -c -trimpath -buildvcs=false -ldflags=-buildid= ./internal/r51x5
Symbol: internal/r51x5.{leaf.function}.abi0
Reference image SHA-256: {symbol.image_sha256}
Symbol bytes SHA-256: {code_sha256}
-/

namespace {leaf.namespace}

def symbolAddress : Nat := {symbol.function.address}
def symbolSize : Nat := {len(symbol.function.data)}
def symbolBytes : List Nat := {nat_list(symbol.function.data)}

{constant_definitions}

end {leaf.namespace}
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--elf", type=Path, required=True)
    parser.add_argument("--leaf", choices=sorted(LEAVES), default="mul")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()

    leaf = LEAVES[arguments.leaf]
    generated = render(extract(arguments.elf.read_bytes(), leaf), leaf)
    if arguments.output is not None:
        arguments.output.write_text(generated, encoding="ascii")
        return
    if arguments.check:
        committed = leaf.generated.read_text(encoding="ascii")
        if committed != generated:
            sys.stderr.writelines(
                difflib.unified_diff(
                    committed.splitlines(keepends=True),
                    generated.splitlines(keepends=True),
                    fromfile="committed Lean input",
                    tofile="generated from the supplied image",
                )
            )
            fail("Go-linked bytes differ from the committed Lean artifact")
        print(f"OK: Go-linked {leaf.description} bytes match committed Lean input")
        return
    sys.stdout.write(generated)


if __name__ == "__main__":
    main()
