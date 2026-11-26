#!/usr/bin/env python3
"""Require the Go r51 symbol check to reject single-point mutations.

Each case edits one aspect of a linked Go image in a temporary copy and
requires `check_go_r51_symbol.py` to exit nonzero. The unmodified image must
pass. Mutations are placed through the image's own symbol table so they hit
the multiplier and its constants, not a look-alike.
"""

from __future__ import annotations

import argparse
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

from generate_go_r51_object_bytes import (
    ELF_HEADER,
    FOLD19,
    LEAVES,
    MASK51,
    SECTION_HEADER,
    SHT_SYMTAB,
    GoElf,
)

PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")
PT_LOAD = 1
PT_DYNAMIC = 2
PT_GNU_STACK = 0x6474E551
SHT_RELR = 19
DT_NEEDED, DT_RELRSZ, DT_RELR = 1, 35, 36
PF_X, PF_W = 1, 2

FUNCTION = LEAVES["mul"].symbol
NORMALIZE = LEAVES["normalize"].symbol
ADD = LEAVES["add"].symbol
SUBTRACT = LEAVES["subtract"].symbol
NEGATE = LEAVES["negate"].symbol

CHECK = Path(__file__).resolve().parent / "check_go_r51_symbol.py"


def file_offset(elf: GoElf, name: str) -> tuple[int, int, int]:
    _info, section_index, value, size = elf.find({name})[name]
    section = elf.sections[section_index]
    return section[4] + value - section[3], value, size


def run(image: bytes) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile(suffix=".elf") as handle:
        handle.write(image)
        handle.flush()
        result = subprocess.run(
            [sys.executable, str(CHECK), "--elf", handle.name],
            capture_output=True,
            text=True,
            check=False,
        )
    lines = (result.stderr or result.stdout).strip().splitlines()
    return result.returncode, lines[-1] if lines else ""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--elf", type=Path, required=True)
    arguments = parser.parse_args()

    original = arguments.elf.read_bytes()
    elf = GoElf(original)
    code, code_address, code_size = file_offset(elf, FUNCTION)
    norm, norm_address, norm_size = file_offset(elf, NORMALIZE)
    add, _, _ = file_offset(elf, ADD)
    subtract, _, _ = file_offset(elf, SUBTRACT)
    negate, _, _ = file_offset(elf, NEGATE)
    fold, fold_address, _ = file_offset(elf, FOLD19)
    mask, mask_address, _ = file_offset(elf, MASK51)

    status, _ = run(original)
    if status != 0:
        raise SystemExit("unmodified image was rejected")

    # Locate the multiplier's two displacement fields from the image itself.
    def site(target: int) -> int:
        sites = [
            offset
            for offset in range(code_size - 3)
            if code_address + offset + 4
            + struct.unpack_from("<i", original, code + offset)[0]
            == target
        ]
        if len(sites) != 1:
            raise SystemExit("could not locate a unique displacement field")
        return sites[0]

    fold_site, mask_site = site(fold_address), site(mask_address)

    def patched(offset: int, data: bytes) -> bytes:
        image = bytearray(original)
        image[offset : offset + len(data)] = data
        return bytes(image)

    def flipped(offset: int) -> bytes:
        return patched(offset, bytes([original[offset] ^ 1]))

    def displaced(field: int, delta: int) -> bytes:
        value = struct.unpack_from("<i", original, code + field)[0] + delta
        return patched(code + field, struct.pack("<i", value))

    def load_header(address: int) -> int:
        """File offset of the PT_LOAD program header that maps `address`."""
        fields = ELF_HEADER.unpack_from(original)
        for index in range(fields[10]):
            offset = fields[5] + index * PROGRAM_HEADER.size
            kind, _flags, _off, vaddr, _paddr, file_size, _mem, _align = (
                PROGRAM_HEADER.unpack_from(original, offset)
            )
            if kind == PT_LOAD and vaddr <= address < vaddr + file_size:
                return offset
        raise SystemExit(f"no PT_LOAD maps {address:#x}")

    def with_flags(image: bytes, address: int, extra: int) -> bytes:
        offset = load_header(address) + 4
        flags = struct.unpack_from("<I", image, offset)[0] | extra
        result = bytearray(image)
        struct.pack_into("<I", result, offset, flags)
        return bytes(result)

    def truncated_before(image: bytes, address: int) -> bytes:
        """Shrink the segment's file-backed size so `address` is not loaded."""
        offset = load_header(address)
        vaddr = PROGRAM_HEADER.unpack_from(image, offset)[3]
        result = bytearray(image)
        struct.pack_into("<Q", result, offset + 32, address - vaddr)
        return bytes(result)

    def unloaded_scratch(size: int) -> int:
        """File offset of `size` bytes in a non-allocated section (debug data
        the loader never maps), so writing there changes nothing the checker
        reads unless a mutation points it there."""
        fields = ELF_HEADER.unpack_from(original)
        for index in range(fields[12]):
            header = SECTION_HEADER.unpack_from(original, fields[6] + index * SECTION_HEADER.size)
            if header[1] == 1 and header[2] & 2 == 0 and header[5] >= size:
                return fields[6] + index * SECTION_HEADER.size, header[4]
        raise SystemExit("no unloaded section large enough for a scratch table")

    def with_relr_section(image: bytes, target: int) -> bytes:
        """Turn an unloaded section into a one-entry RELR table for `target`."""
        header, offset = unloaded_scratch(8)
        result = bytearray(image)
        struct.pack_into("<I", result, header + 4, SHT_RELR)
        struct.pack_into("<Q", result, header + 32, 8)
        struct.pack_into("<Q", result, offset, target)
        return bytes(result)

    def with_dynamic_relr(image: bytes, target: int) -> bytes:
        """Add a PT_DYNAMIC whose DT_RELR table, at a loaded address the checker
        does not otherwise read, relocates `target`."""
        fields = ELF_HEADER.unpack_from(image)
        stack = None
        for index in range(fields[10]):
            offset = fields[5] + index * PROGRAM_HEADER.size
            if PROGRAM_HEADER.unpack_from(image, offset)[0] == PT_GNU_STACK:
                stack = offset
        if stack is None:
            raise SystemExit("no PT_GNU_STACK header to repurpose")
        _header, table_offset = unloaded_scratch(96)
        table_address = norm_address + norm_size  # code padding after a leaf
        table_file = norm + norm_size
        result = bytearray(image)
        # Two DT_NEEDED entries first: a dynamically linked binary repeats that
        # tag, and the checker must still read the relocation table after it.
        struct.pack_into("<IIQQQQQQ", result, stack, PT_DYNAMIC, 4, table_offset, 0, 0, 80, 80, 8)
        struct.pack_into(
            "<10Q", result, table_offset,
            DT_NEEDED, 1, DT_NEEDED, 2, DT_RELRSZ, 8, DT_RELR, table_address, 0, 0,
        )
        struct.pack_into("<Q", result, table_file, target)
        return bytes(result)

    def stripped(image: bytes) -> bytes:
        """Hide the symbol table so the checker falls back to byte search."""
        fields = ELF_HEADER.unpack_from(image)
        result = bytearray(image)
        for index in range(fields[12]):
            offset = fields[6] + index * SECTION_HEADER.size
            if SECTION_HEADER.unpack_from(image, offset)[1] == SHT_SYMTAB:
                struct.pack_into("<I", result, offset + 4, 0)
        return bytes(result)

    status, message = run(stripped(original))
    if status != 0:
        raise SystemExit(f"unmodified image without a symbol table was rejected: {message}")

    # Layout of the vector body after the 15-byte prelude: ten loads (two of
    # six bytes, eight of seven), eighteen six-byte clears, then six-byte
    # IFMA products. `product` is the ninth product instruction.
    product = code + 15 + 68 + 108 + 6 * 8
    final_store_displacement = code + code_size - 5
    expected = {
        code + 4: 0x08,  # disp8 of MOVQ 8(SP), DI
        code + 15 + 5: 0x01,  # ModRM of VMOVDQU64 0(CX), Z0
        product + 4: 0xB4,  # VPMADD52LUQ opcode
        final_store_displacement: 0x04,  # compressed disp8 of the last store
        code + code_size - 1: 0xC3,  # RET
        # Normalizer: 10-byte prelude, five loads (6 + 4 * 7), two 10-byte
        # broadcasts, then VPSRLQ $51 with its immediate as the seventh byte.
        norm + 9: 0x10,  # disp8 of MOVQ 16(SP), CX
        norm + 10 + 34 + 20 + 6: 51,  # carry shift count
        norm + norm_size - 5: 0x04,  # compressed disp8 of the last store
        # Adder: 15-byte prelude, five loads, then VPADDQ 0(BX), Z0, Z0.
        add + 15 + 34 + 4: 0xD4,
        # Subtractor: prelude, five loads, two broadcasts, five register
        # adds, then VPSUBQ 0(BX), Z0, Z0.
        subtract + 15 + 34 + 20 + 30 + 4: 0xFB,
        # Negator: 10-byte prelude, then VPBROADCASTQ ifmaSubBias0, Z0.
        negate + 10 + 4: 0x59,
    }
    for offset, value in expected.items():
        if original[offset] != value:
            raise SystemExit(
                f"image layout changed: byte at symbol offset {offset - code} "
                f"is {original[offset]:#x}, expected {value:#x}"
            )

    def negative_target(field: int) -> bytes:
        """Point a displacement field backwards; any negative value must fail."""
        return patched(code + field, struct.pack("<i", -16))

    # Cases whose rejection must come from a specific check carry its message.
    targeted = {
        "code segment made writable": (
            with_flags(original, code_address, PF_W), "not read-only"
        ),
        "constant segment made executable": (
            with_flags(original, fold_address, PF_X), "execute permission"
        ),
        "code outside the file-backed segment": (
            truncated_before(original, code_address), "file-backed"
        ),
        "no symbol table, code outside the file-backed segment": (
            truncated_before(stripped(original), code_address), "loaded candidate"
        ),
        "fold displacement negative": (negative_target(fold_site), "negative displacement"),
        "RELR section relocates the code": (
            with_relr_section(original, code_address + 16), "relocation"
        ),
        "PT_DYNAMIC RELR table relocates a constant": (
            with_dynamic_relr(original, fold_address), "relocation"
        ),
    }

    cases = {
        "argument stack slot": flipped(code + 4),
        "argument destination register": flipped(code + 7),
        "first source-load base register": flipped(code + 15 + 5),
        "IFMA low opcode to high": patched(product + 4, b"\xb5"),
        "product source register": flipped(product + 5),
        "final store displacement": flipped(final_store_displacement),
        "ret replaced by nop": patched(code + code_size - 1, b"\x90"),
        "fold constant 19 -> 18": patched(fold, b"\x12"),
        "mask constant low byte": flipped(mask),
        "fold displacement retargeted to mask": displaced(
            fold_site, mask_address - fold_address
        ),
        "mask displacement retargeted by 8": displaced(mask_site, 16),
        "normalizer argument stack slot": flipped(norm + 9),
        "normalizer carry shift count": flipped(norm + 10 + 34 + 20 + 6),
        "normalizer final store displacement": flipped(norm + norm_size - 5),
        "adder memory add to subtract": patched(add + 15 + 34 + 4, b"\xfb"),
        "subtractor memory subtract to add": patched(
            subtract + 15 + 34 + 20 + 30 + 4, b"\xd4"
        ),
        "negator limb-zero bias retargeted to the other bias": patched(
            negate + 16,
            struct.pack(
                "<i", struct.unpack_from("<i", original, negate + 16)[0] + 8
            ),
        ),
    }
    failures = []
    for name, image in cases.items():
        status, message = run(image)
        if status == 0:
            failures.append(name)
        else:
            print(f"OK: mutation {name} rejected: {message[:96]}")
    for name, (image, reason) in targeted.items():
        status, message = run(image)
        if status == 0 or reason not in message:
            failures.append(f"{name} (status {status}: {message[:96]})")
        else:
            print(f"OK: mutation {name} rejected: {message[:96]}")
    if failures:
        raise SystemExit(f"mutations not rejected as expected: {failures}")
    total = len(cases) + len(targeted)
    print(f"PASS: all {total} Go r51 symbol mutations were rejected")


if __name__ == "__main__":
    main()
