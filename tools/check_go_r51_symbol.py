#!/usr/bin/env python3
"""Check that a linked binary contains the proved Go r51 leaf bytes.

For each covered leaf (`LEAVES` in `generate_go_r51_object_bytes.py`) a Lean
module proves a leaf theorem about the exact committed bytes, and a
`..._refines_relocated` theorem extends it to any link layout: the same code
with its constant-broadcast addresses (two or four per leaf) renamed.

Two builds of the same Go assembly differ only in the RIP-relative
displacement fields that address the constants. This tool checks exactly that
for an arbitrary linked ELF64 x86-64 image, for example a validator binary:

1. each leaf symbol has the reference length and the reference bytes
   everywhere outside those displacement fields;
2. each displacement field holds a nonnegative signed disp32, the only form
   the Lean decoder accepts, and resolves to a qword in allocated,
   non-writable, non-executable memory;
3. those qwords hold the values the leaf's specification declares.

Every byte checked (code and constants) is read through the image's program
headers, not only its sections: it must lie in the file-backed part of
exactly one PT_LOAD segment, readable and not writable, executable for code
and not executable for constants, with no other PT_LOAD sharing its pages.
Where sections exist the section bytes must agree. No REL, RELA, or RELR
relocation, whether listed in a section or in the PT_DYNAMIC table, may
relocate a checked byte.

It prints the constant addresses, which are the address arguments of the
relocated Lean theorem for that image.

If the image has no symbol table the symbol is located by searching the
file-backed bytes of executable PT_LOAD segments for the reference bytes with
those fields as wildcards; exactly one match is required.

Not checked here: that the image's callers reach this symbol (a loaded match
does not prove runtime dispatch), the Go-compiled wrapper, CPU dispatch, or
any other leaf. Relocations are read from REL, RELA, and RELR sections and from
the PT_DYNAMIC table (DT_RELA, DT_REL, DT_RELR, DT_JMPREL); other packed
formats (for example Android APS2) are not decoded. The step from "bytes equal outside
the displacement fields" to "the decoded program is the reference program with
renamed addresses" relies on the decoder treating a displacement uniformly; it
is closed in Lean for an image by regenerating the Lean input from that image.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import struct
from pathlib import Path
from typing import NoReturn

import generate_go_r51_object_bytes as reference_tool
from generate_go_r51_object_bytes import (
    CONSTANT_VALUES,
    ELF_HEADER,
    LEAVES,
    SHF_ALLOC,
    SHF_EXECINSTR,
    SHF_WRITE,
    SHT_PROGBITS,
    SHT_SYMTAB,
    GoElf,
    Leaf,
    constant_symbol,
)

PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")
PT_LOAD = 1
PT_DYNAMIC = 2
PF_X, PF_W, PF_R = 1, 2, 4
SHT_RELA, SHT_REL, SHT_RELR = 4, 9, 19
DT_NULL, DT_PLTRELSZ, DT_RELA, DT_RELASZ = 0, 2, 7, 8
DT_REL, DT_RELSZ, DT_PLTREL, DT_JMPREL = 17, 18, 20, 23
DT_RELRSZ, DT_RELR = 35, 36
RELOCATION_TAGS = {
    DT_RELA, DT_RELASZ, DT_REL, DT_RELSZ, DT_RELR, DT_RELRSZ, DT_JMPREL, DT_PLTRELSZ, DT_PLTREL
}
PAGE = 4096


def fail(message: str) -> NoReturn:
    raise SystemExit(f"Go r51 symbol check failed: {message}")


def lean_nat(text: str, name: str) -> int:
    match = re.search(rf"^def {name} : Nat := (\d+)$", text, re.MULTILINE)
    if match is None:
        fail(f"committed Lean input has no definition {name}")
    return int(match.group(1))


def lean_bytes(text: str, name: str) -> bytes:
    match = re.search(
        rf"^def {name} : List Nat := \[(.*?)\]$", text, re.MULTILINE | re.DOTALL
    )
    if match is None:
        fail(f"committed Lean input has no byte list {name}")
    values = [int(item) for item in match.group(1).replace("\n", " ").split(",")]
    if any(value < 0 or value > 255 for value in values):
        fail(f"{name} contains a non-byte value")
    return bytes(values)


def displacement_site(code: bytes, symbol_address: int, target: int, label: str) -> int:
    """Offset of the unique disp32 field whose RIP-relative target is `target`."""
    sites = [
        offset
        for offset in range(len(code) - 3)
        if symbol_address + offset + 4
        + struct.unpack_from("<i", code, offset)[0]
        == target
    ]
    if len(sites) != 1:
        fail(f"reference bytes have {len(sites)} displacement sites for {label}")
    return sites[0]


class LoadMap:
    """The image's PT_LOAD segments: what the loader actually maps."""

    def __init__(self, image: bytes) -> None:
        self.image = image
        fields = ELF_HEADER.unpack_from(image)
        offset, entry_size, count = fields[5], fields[9], fields[10]
        if count == 0 or entry_size != PROGRAM_HEADER.size:
            fail("unsupported program header table")
        if offset + count * entry_size > len(image):
            fail("program header table extends beyond image")
        self.segments = []
        self.dynamic: list[tuple[int, int]] = []
        for index in range(count):
            kind, flags, file_offset, vaddr, _paddr, file_size, memory_size, align = (
                PROGRAM_HEADER.unpack_from(image, offset + index * entry_size)
            )
            if kind == PT_DYNAMIC:
                if file_offset + file_size > len(image):
                    fail("PT_DYNAMIC extends beyond image")
                self.dynamic.append((file_offset, file_size))
            if kind != PT_LOAD:
                continue
            if file_size > memory_size or file_offset + file_size > len(image):
                fail(f"PT_LOAD at {vaddr:#x} has an invalid file extent")
            if align > 1 and (vaddr - file_offset) % align != 0:
                fail(f"PT_LOAD at {vaddr:#x} is not congruent to its file offset")
            self.segments.append((flags, file_offset, vaddr, file_size, memory_size))
        if not self.segments:
            fail("image has no PT_LOAD segments")

    def read(self, address: int, size: int, label: str, *, executable: bool) -> bytes:
        """Bytes at `address` as the loader maps them, with required permissions."""
        covering = [
            segment
            for segment in self.segments
            if segment[2] <= address and address + size <= segment[2] + segment[3]
        ]
        if len(covering) != 1:
            fail(
                f"{label} at {address:#x} is not in the file-backed part of exactly "
                f"one PT_LOAD segment ({len(covering)} found)"
            )
        flags, file_offset, vaddr, _file_size, _memory_size = covering[0]
        if not flags & PF_R or flags & PF_W:
            fail(f"{label} at {address:#x} is in a PT_LOAD segment that is not read-only")
        if bool(flags & PF_X) != executable:
            fail(
                f"{label} at {address:#x} is in a PT_LOAD segment whose execute "
                "permission is wrong"
            )
        first_page = address // PAGE
        last_page = (address + size - 1) // PAGE
        for other in self.segments:
            if other is covering[0] or other[4] == 0:
                continue
            if other[2] // PAGE <= last_page and first_page <= (other[2] + other[4] - 1) // PAGE:
                fail(f"{label} at {address:#x} shares a page with another PT_LOAD segment")
        start = file_offset + address - vaddr
        return self.image[start : start + size]

    def mapped(self, address: int, size: int, label: str) -> bytes:
        """File-backed bytes at a virtual address, whatever the permissions."""
        for _flags, file_offset, vaddr, file_size, _memory_size in self.segments:
            if vaddr <= address and address + size <= vaddr + file_size:
                start = file_offset + address - vaddr
                return self.image[start : start + size]
        fail(f"{label} at {address:#x} is not in the file-backed part of a PT_LOAD segment")

    def executable_ranges(self):
        for flags, file_offset, vaddr, file_size, _memory_size in self.segments:
            if flags & PF_X and flags & PF_R and not flags & PF_W:
                yield vaddr, self.image[file_offset : file_offset + file_size]


def explicit_targets(data: bytes, entry_size: int) -> list[int]:
    """r_offset of each REL (16-byte) or RELA (24-byte) entry."""
    if len(data) % entry_size:
        fail("relocation table size is not a multiple of its entry size")
    return [
        struct.unpack_from("<Q", data, offset)[0]
        for offset in range(0, len(data), entry_size)
    ]


def relr_targets(data: bytes) -> list[int]:
    """Decode a packed RELR table: an even word is an address, an odd word a
    bitmap of the following 63 words."""
    if len(data) % 8:
        fail("RELR table size is not a multiple of 8")
    targets: list[int] = []
    following = None
    for offset in range(0, len(data), 8):
        word = struct.unpack_from("<Q", data, offset)[0]
        if word & 1 == 0:
            targets.append(word)
            following = word + 8
            continue
        if following is None:
            fail("RELR bitmap without a preceding address")
        for bit in range(1, 64):
            if word >> bit & 1:
                targets.append(following + (bit - 1) * 8)
        following += 63 * 8
    return targets


def dynamic_targets(loads: LoadMap) -> list[int]:
    """Relocation targets named by the dynamic table, which the loader uses
    whether or not section headers describe them."""
    targets: list[int] = []
    for file_offset, file_size in loads.dynamic:
        tags: dict[int, int] = {}
        for offset in range(file_offset, file_offset + file_size - 15, 16):
            tag, value = struct.unpack_from("<QQ", loads.image, offset)
            if tag == DT_NULL:
                break
            # Tags such as DT_NEEDED legitimately repeat; the relocation tags
            # read below must not, or a second table could go unchecked.
            if tag in RELOCATION_TAGS and tag in tags:
                fail(f"dynamic table repeats relocation tag {tag}")
            tags[tag] = value
        tables = [
            (DT_RELA, DT_RELASZ, "rela"),
            (DT_REL, DT_RELSZ, "rel"),
            (DT_RELR, DT_RELRSZ, "relr"),
        ]
        if DT_JMPREL in tags:
            kind = tags.get(DT_PLTREL)
            if kind not in (DT_RELA, DT_REL):
                fail("DT_JMPREL without a valid DT_PLTREL")
            tables.append((DT_JMPREL, DT_PLTRELSZ, "rela" if kind == DT_RELA else "rel"))
        for address_tag, size_tag, form in tables:
            if (address_tag in tags) != (size_tag in tags):
                fail(f"dynamic table has tag {address_tag} without its size")
            if address_tag not in tags:
                continue
            data = loads.mapped(tags[address_tag], tags[size_tag], "dynamic relocation table")
            if form == "relr":
                targets += relr_targets(data)
            else:
                targets += explicit_targets(data, 24 if form == "rela" else 16)
    return targets


def reject_relocations(
    elf: GoElf, loads: LoadMap, ranges: list[tuple[int, int, str]]
) -> None:
    """Fail if any REL, RELA, or RELR entry, from a section or from the
    dynamic table, writes into a checked range."""
    targets = dynamic_targets(loads)
    for section in elf.sections:
        data = None
        if section[1] in (SHT_RELA, SHT_REL, SHT_RELR):
            data = elf.slice(section[4], section[5], "relocation section")
        if section[1] == SHT_RELA:
            targets += explicit_targets(data, 24)
        elif section[1] == SHT_REL:
            targets += explicit_targets(data, 16)
        elif section[1] == SHT_RELR:
            targets += relr_targets(data)
    for target in targets:
        for start, size, label in ranges:
            if target < start + size and start < target + 8:
                fail(f"a relocation at {target:#x} writes into {label}")


def section_of(elf: GoElf, address: int, size: int):
    for section in elf.sections:
        if section[1] != SHT_PROGBITS or not section[2] & SHF_ALLOC:
            continue
        if section[3] <= address and address + size <= section[3] + section[5]:
            return section
    return None


def read_constant(elf: GoElf, loads: LoadMap, address: int, label: str) -> int:
    data = loads.read(address, 8, label, executable=False)
    section = section_of(elf, address, 8)
    if section is None:
        fail(f"{label} at {address:#x} is not in allocated PROGBITS")
    if section[2] & (SHF_WRITE | SHF_EXECINSTR):
        fail(f"{label} at {address:#x} is in writable or executable memory")
    if elf.slice(section[4] + address - section[3], 8, label) != data:
        fail(f"{label} at {address:#x}: section and loaded bytes differ")
    return int.from_bytes(data, "little")


def locate(
    elf: GoElf, loads: LoadMap, leaf: Leaf, pattern: bytes, wildcard: set[int]
) -> tuple[int, bytes, str]:
    if any(section[1] == SHT_SYMTAB for section in elf.sections):
        entries = elf.find({leaf.symbol})
        symbol = elf.symbol_bytes(entries[leaf.symbol], leaf.symbol, executable=True)
        loaded = loads.read(symbol.address, len(symbol.data), leaf.function, executable=True)
        if loaded != symbol.data:
            fail(f"{leaf.function}: section and loaded bytes differ")
        return symbol.address, loaded, "symbol table"
    fixed = [index for index in range(len(pattern)) if index not in wildcard]
    anchor = pattern[: min(wildcard)]
    matches = []
    for segment_address, text in loads.executable_ranges():
        start = text.find(anchor)
        while start >= 0:
            window = text[start : start + len(pattern)]
            if len(window) == len(pattern) and all(
                window[index] == pattern[index] for index in fixed
            ):
                matches.append((segment_address + start, window))
            start = text.find(anchor, start + 1)
    if len(matches) != 1:
        fail(f"byte search found {len(matches)} loaded candidate symbols, expected 1")
    address = matches[0][0]
    loaded = loads.read(address, len(pattern), leaf.function, executable=True)
    return address, loaded, "byte search"


def check(leaf: Leaf, image: bytes) -> None:
    committed = leaf.generated.read_text(encoding="ascii")
    reference = lean_bytes(committed, "symbolBytes")
    reference_address = lean_nat(committed, "symbolAddress")
    if len(reference) != lean_nat(committed, "symbolSize"):
        fail("committed symbol size does not match its byte list")
    sites = {
        name: displacement_site(
            reference, reference_address, lean_nat(committed, f"{name}Address"), name
        )
        for name in leaf.constants
    }
    wildcard: set[int] = set()
    for site in sites.values():
        wildcard |= set(range(site, site + 4))
    if len(wildcard) != 4 * len(sites):
        fail("reference displacement fields overlap")

    for site in sites.values():
        if struct.unpack_from("<i", reference, site)[0] < 0:
            fail("reference has a negative displacement")

    elf = GoElf(image)
    loads = LoadMap(image)
    address, code, method = locate(elf, loads, leaf, reference, wildcard)
    if len(code) != len(reference):
        fail(f"{leaf.function} is {len(code)} bytes, reference is {len(reference)}")
    differing = [
        index
        for index in range(len(reference))
        if index not in wildcard and code[index] != reference[index]
    ]
    if differing:
        fail(
            f"{leaf.function}: {len(differing)} bytes differ outside the "
            "displacement fields, "
            f"first at offset {differing[0]}"
        )

    def target(site: int, label: str) -> int:
        displacement = struct.unpack_from("<i", code, site)[0]
        # X86Decoder.decodeBroadcast admits only a nonnegative signed disp32.
        if displacement < 0:
            fail(f"{label} has a negative displacement, which the Lean decoder rejects")
        return address + site + 4 + displacement

    targets = {name: target(site, name) for name, site in sites.items()}
    if len(set(targets.values())) != len(targets):
        fail("two displacement fields resolve to the same address")
    for name, address_of in targets.items():
        if read_constant(elf, loads, address_of, name) != CONSTANT_VALUES[name]:
            fail(f"qword at {address_of:#x} is not {name} = {CONSTANT_VALUES[name]}")
    reject_relocations(
        elf,
        loads,
        [(address, len(code), leaf.function)]
        + [(address_of, 8, name) for name, address_of in targets.items()],
    )
    if any(section[1] == SHT_SYMTAB for section in elf.sections):
        symbols = {name: constant_symbol(name) for name in targets}
        named = elf.find(set(symbols.values()))
        for name, target in targets.items():
            if named[symbols[name]][2] != target:
                fail(f"displacement target for {name} is not the named symbol")

    normalized = bytearray(code)
    for index in wildcard:
        normalized[index] = 0
    print(f"OK: proved Go r51 {leaf.description} bytes present (located by {method})")
    print(f"  image sha256        {hashlib.sha256(image).hexdigest()}")
    print(f"  symbol address      {address:#x}, {len(code)} bytes")
    print(f"  normalized sha256   {hashlib.sha256(bytes(normalized)).hexdigest()}")
    for name in leaf.constants:
        print(
            f"  {name:<19} address {targets[name]}, displacement field at "
            f"offset {sites[name]}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--elf", type=Path, required=True)
    parser.add_argument(
        "--leaf", choices=sorted(LEAVES), action="append",
        help="leaf to check (default: every covered leaf)",
    )
    arguments = parser.parse_args()
    image = arguments.elf.read_bytes()
    for name in arguments.leaf or sorted(LEAVES):
        check(LEAVES[name], image)
    _ = reference_tool


if __name__ == "__main__":
    main()
