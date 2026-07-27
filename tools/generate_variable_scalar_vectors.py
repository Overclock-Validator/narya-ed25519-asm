#!/usr/bin/env python3
"""Generate full-width variable-base scalar-multiplication fixtures."""

import argparse
import random

from generate_basepoint_multiples import BASE_X, BASE_Y, add, compress

L = 2**252 + 27742317777372353535851937790883648493


def scalar_mult(scalar, point):
    result = (0, 1)
    addend = point
    while scalar:
        if scalar & 1:
            result = add(result, addend)
        addend = add(addend, addend)
        scalar >>= 1
    return result


def negate(point):
    x, y = point
    return (-x) % (2**255 - 19), y


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-groups", type=int, default=32)
    args = parser.parse_args()
    if args.groups < 1:
        raise SystemExit("groups must be positive")

    bases = []
    current = (0, 1)
    for _ in range(8):
        current = add(current, (BASE_X, BASE_Y))
        bases.append(current)

    edges = [0, 1, 2, 15, 16, 17, 2**251, 2**252, L - 2, L - 1]
    rng = random.Random(0x4E41525941584D38)
    print("# narya-variable-scalar-mult-v1")
    print("# group lane base_index scalar_le_hex negative expected_hex")
    for group in range(args.groups):
        for lane, base in enumerate(bases):
            position = group * 8 + lane
            scalar = edges[position] if position < len(edges) else rng.randrange(L)
            negative = (group * 3 + lane) & 1
            result = scalar_mult(scalar, base)
            if negative:
                result = negate(result)
            print(
                group,
                lane,
                lane + 1,
                scalar.to_bytes(32, "little").hex(),
                negative,
                compress(result),
            )


if __name__ == "__main__":
    main()
