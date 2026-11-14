#!/usr/bin/env python3
"""Check that a linked binary contains the proved Go r51 leaf bytes.

For each covered leaf (`LEAVES` in `generate_go_r51_object_bytes.py`) a Lean
module proves a leaf theorem about the exact committed bytes, and a
`..._refines_relocated` theorem extends it to any link layout: the same code
with its two constant-broadcast addresses renamed.

Two builds of the same Go assembly differ only in the two RIP-relative
displacement fields that address the constants. This tool checks exactly that
for an arbitrary linked ELF64 x86-64 image, for example a validator binary:

1. each leaf symbol has the reference length and the reference bytes
   everywhere outside the two displacement fields;
2. each displacement field resolves to a qword in allocated, non-writable,
   non-executable memory;
3. those qwords hold 19 and 2^51-1.

It prints the two constant addresses, which are the `fold19` and `mask51`
arguments of the relocated Lean theorem for that image.

If the image has no symbol table the symbol is located by searching executable
sections for the reference bytes with the two fields as wildcards; exactly one
match is required.

Not checked here: that the image's callers reach this symbol, the Go-compiled
wrapper, CPU dispatch, or any other leaf. The step from "bytes equal outside
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
    FOLD19,
    LEAVES,
    MASK51,
    SHF_ALLOC,
    SHF_EXECINSTR,
    SHF_WRITE,
    SHT_PROGBITS,
    SHT_SYMTAB,
    GoElf,
    Leaf,
)

FOLD19_VALUE = 19
MASK51_VALUE = (1 << 51) - 1


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


def section_of(elf: GoElf, address: int, size: int):
    for section in elf.sections:
        if section[1] != SHT_PROGBITS or not section[2] & SHF_ALLOC:
            continue
        if section[3] <= address and address + size <= section[3] + section[5]:
            return section
    return None


def read_constant(elf: GoElf, address: int, label: str) -> int:
    section = section_of(elf, address, 8)
    if section is None:
        fail(f"{label} at {address:#x} is not in allocated PROGBITS")
    if section[2] & (SHF_WRITE | SHF_EXECINSTR):
        fail(f"{label} at {address:#x} is in writable or executable memory")
    data = elf.slice(section[4] + address - section[3], 8, label)
    return int.from_bytes(data, "little")


def locate(
    elf: GoElf, leaf: Leaf, pattern: bytes, wildcard: set[int]
) -> tuple[int, bytes, str]:
    if any(section[1] == SHT_SYMTAB for section in elf.sections):
        entries = elf.find({leaf.symbol})
        symbol = elf.symbol_bytes(entries[leaf.symbol], leaf.symbol, executable=True)
        return symbol.address, symbol.data, "symbol table"
    fixed = [index for index in range(len(pattern)) if index not in wildcard]
    anchor = pattern[: min(wildcard)]
    matches = []
    for section in elf.sections:
        if section[1] != SHT_PROGBITS or not section[2] & SHF_EXECINSTR:
            continue
        text = elf.slice(section[4], section[5], "executable section")
        start = text.find(anchor)
        while start >= 0:
            window = text[start : start + len(pattern)]
            if len(window) == len(pattern) and all(
                window[index] == pattern[index] for index in fixed
            ):
                matches.append((section[3] + start, window))
            start = text.find(anchor, start + 1)
    if len(matches) != 1:
        fail(f"byte search found {len(matches)} candidate symbols, expected 1")
    return matches[0][0], matches[0][1], "byte search"


def check(leaf: Leaf, image: bytes) -> None:
    committed = leaf.generated.read_text(encoding="ascii")
    reference = lean_bytes(committed, "symbolBytes")
    reference_address = lean_nat(committed, "symbolAddress")
    if len(reference) != lean_nat(committed, "symbolSize"):
        fail("committed symbol size does not match its byte list")
    fold_site = displacement_site(
        reference, reference_address, lean_nat(committed, "ifmaFold19Address"), "fold19"
    )
    mask_site = displacement_site(
        reference,
        reference_address,
        lean_nat(committed, "ifmaLimbMask51Address"),
        "mask51",
    )
    wildcard = set(range(fold_site, fold_site + 4)) | set(range(mask_site, mask_site + 4))
    if len(wildcard) != 8:
        fail("reference displacement fields overlap")

    elf = GoElf(image)
    address, code, method = locate(elf, leaf, reference, wildcard)
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

    def target(site: int) -> int:
        return address + site + 4 + struct.unpack_from("<i", code, site)[0]

    fold_address, mask_address = target(fold_site), target(mask_site)
    if fold_address == mask_address:
        fail("both displacement fields resolve to the same address")
    if read_constant(elf, fold_address, "fold19") != FOLD19_VALUE:
        fail(f"qword at {fold_address:#x} is not 19")
    if read_constant(elf, mask_address, "mask51") != MASK51_VALUE:
        fail(f"qword at {mask_address:#x} is not 2^51-1")
    if any(section[1] == SHT_SYMTAB for section in elf.sections):
        named = elf.find({FOLD19, MASK51})
        if named[FOLD19][2] != fold_address or named[MASK51][2] != mask_address:
            fail("displacement targets are not the named constant symbols")

    normalized = bytearray(code)
    for index in wildcard:
        normalized[index] = 0
    print(f"OK: proved Go r51 {leaf.description} bytes present (located by {method})")
    print(f"  image sha256        {hashlib.sha256(image).hexdigest()}")
    print(f"  symbol address      {address:#x}, {len(code)} bytes")
    print(f"  normalized sha256   {hashlib.sha256(bytes(normalized)).hexdigest()}")
    print(f"  displacement fields offsets {fold_site} and {mask_site}")
    print(f"  fold19 address      {fold_address}  (value 19)")
    print(f"  mask51 address      {mask_address}  (value 2^51-1)")


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
