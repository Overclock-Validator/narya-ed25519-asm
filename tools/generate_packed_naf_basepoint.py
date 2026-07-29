#!/usr/bin/env python3
"""Generate the immutable packed width-8 NAF basepoint table.

The production singleton path stores one affine cached point per positive odd
multiple 1B, 3B, ..., 127B.  This generator deliberately shares no Narya
field or point code: Python integers perform affine Edwards addition modulo p,
then the result is converted to reduced radix-2^51 limbs.

Each 160-byte entry is five rows of four little-endian uint64 values:

    [Y-X, Y+X, 2dXY, 2]

The four values are the coordinate-parallel lanes consumed by packed_x4.c.
"""

from __future__ import annotations

import argparse
import struct
from pathlib import Path


P = 2**255 - 19
D = (-121665 * pow(121666, -1, P)) % P
BASE_X = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BASE_Y = 46316835694926478169428394003475163141307993866256225615783033603165251855960
MASK51 = (1 << 51) - 1


def add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    x1, y1 = left
    x2, y2 = right
    product = D * x1 * x2 * y1 * y2 % P
    x3 = (x1 * y2 + y1 * x2) * pow(1 + product, -1, P) % P
    y3 = (y1 * y2 + x1 * x2) * pow(1 - product, -1, P) % P
    return x3, y3


def limbs(value: int) -> list[int]:
    return [(value >> (51 * index)) & MASK51 for index in range(5)]


def generate() -> bytes:
    base = (BASE_X, BASE_Y)
    twice = add(base, base)
    point = base
    output = bytearray()
    for _ in range(64):
        x, y = point
        coordinates = (
            (y - x) % P,
            (y + x) % P,
            (2 * D * x * y) % P,
            2,
        )
        rows = [limbs(value) for value in coordinates]
        for limb in range(5):
            output.extend(struct.pack("<4Q", *(row[limb] for row in rows)))
        point = add(point, twice)
    assert len(output) == 64 * 5 * 4 * 8
    return bytes(output)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    payload = generate()
    if arguments.output is None:
        import sys

        sys.stdout.buffer.write(payload)
    else:
        arguments.output.write_bytes(payload)


if __name__ == "__main__":
    main()
