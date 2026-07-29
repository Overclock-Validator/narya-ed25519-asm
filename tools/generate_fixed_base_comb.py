#!/usr/bin/env python3
"""Generate the immutable radix-256 Ed25519 basepoint comb and test vectors."""

import argparse
import random
import struct
from pathlib import Path

from generate_basepoint_multiples import BASE_X, BASE_Y, D, P, add, compress

L = 2**252 + 27742317777372353535851937790883648493
MASK51 = (1 << 51) - 1


def scalar_mult(scalar, point):
    result = (0, 1)
    addend = point
    while scalar:
        if scalar & 1:
            result = add(result, addend)
        addend = add(addend, addend)
        scalar >>= 1
    return result


def limbs(value):
    return [(value >> (51 * index)) & MASK51 for index in range(5)]


def affine_entry(point, negative):
    x, y = point
    plus = (y + x) % P
    minus = (y - x) % P
    t2d = (2 * D * x * y) % P
    if negative:
        plus, minus, t2d = minus, plus, (-t2d) % P
    coordinates = [limbs(plus), limbs(minus), limbs(t2d)]
    return b"".join(
        struct.pack("<QQQ", *(coordinates[c][limb] for c in range(3)))
        for limb in range(5)
    )


def build_table():
    output = bytearray()
    position_base = (BASE_X, BASE_Y)
    for position in range(16):
        multiple = (0, 1)
        for _ in range(128):
            multiple = add(multiple, position_base)
            output += affine_entry(multiple, False)
            output += affine_entry(multiple, True)
        if position != 15:
            for _ in range(16):
                position_base = add(position_base, position_base)
    if len(output) != 16 * 128 * 2 * 5 * 3 * 8:
        raise AssertionError("unexpected comb payload size")
    return output


def build_b10_table():
    """Build signed affine-Niels entries for [1]B through [512]B."""
    output = bytearray()
    multiple = (0, 1)
    base = (BASE_X, BASE_Y)
    for _ in range(512):
        multiple = add(multiple, base)
        output += affine_entry(multiple, False)
        output += affine_entry(multiple, True)
    if len(output) != 512 * 2 * 5 * 3 * 8:
        raise AssertionError("unexpected B10 payload size")
    return output


def build_fixtures(groups):
    edges = [0, 1, 2, 127, 128, 129, 2**251, 2**252, L - 2, L - 1]
    rng = random.Random(0x4E41525941434F4D)
    lines = [
        "# narya-fixed-base-scalar-v1",
        "# group lane scalar_le_hex expected_hex",
    ]
    for group in range(groups):
        for lane in range(8):
            position = group * 8 + lane
            scalar = edges[position] if position < len(edges) else rng.randrange(L)
            expected = compress(scalar_mult(scalar, (BASE_X, BASE_Y)))
            lines.append(
                f"{group} {lane} {scalar.to_bytes(32, 'little').hex()} {expected}"
            )
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--vectors", type=Path, required=True)
    parser.add_argument("--b10-table", type=Path)
    parser.add_argument("--groups", type=int, default=32)
    args = parser.parse_args()
    if args.groups < 1:
        raise SystemExit("groups must be positive")
    args.table.write_bytes(build_table())
    if args.b10_table is not None:
        args.b10_table.write_bytes(build_b10_table())
    args.vectors.write_text(build_fixtures(args.groups), encoding="ascii")


if __name__ == "__main__":
    main()
