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

from generate_go_r51_object_bytes import FOLD19, FUNCTION, MASK51, GoElf

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
    fold, fold_address, _ = file_offset(elf, FOLD19)
    mask, mask_address, _ = file_offset(elf, MASK51)

    status, _ = run(original)
    if status != 0:
        raise SystemExit("unmodified image was rejected")

    # Locate the two displacement fields from the image itself.
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
    }
    for offset, value in expected.items():
        if original[offset] != value:
            raise SystemExit(
                f"image layout changed: byte at symbol offset {offset - code} "
                f"is {original[offset]:#x}, expected {value:#x}"
            )

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
    }
    failures = []
    for name, image in cases.items():
        status, message = run(image)
        if status == 0:
            failures.append(name)
        else:
            print(f"OK: mutation {name} rejected: {message[:96]}")
    if failures:
        raise SystemExit(f"mutations accepted: {failures}")
    print(f"PASS: all {len(cases)} Go r51 symbol mutations were rejected")


if __name__ == "__main__":
    main()
