#!/usr/bin/env python3
"""Generate independent affine Edwards25519 basepoint-multiple fixtures.

This tool intentionally shares no Narya field representation or projective
formula. Python integers perform every operation modulo p, affine addition
uses explicit inversions, and output is ordinary compressed Edwards y plus
the parity of x. It is a fixture generator, not production code.
"""

import argparse

P = 2**255 - 19
D = (-121665 * pow(121666, -1, P)) % P
BASE_X = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BASE_Y = 46316835694926478169428394003475163141307993866256225615783033603165251855960


def add(p, q):
    x1, y1 = p
    x2, y2 = q
    product = (D * x1 * x2 * y1 * y2) % P
    x3 = ((x1 * y2 + y1 * x2) * pow(1 + product, -1, P)) % P
    y3 = ((y1 * y2 + x1 * x2) * pow(1 - product, -1, P)) % P
    return x3, y3


def compress(point):
    x, y = point
    encoded = bytearray(y.to_bytes(32, "little"))
    encoded[31] |= (x & 1) << 7
    return encoded.hex()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-count", type=int, default=128)
    args = parser.parse_args()
    if args.count < 1:
        raise SystemExit("count must be positive")

    print("# narya-affine-basepoint-multiples-v1")
    print("# n compressed_edwards_y_hex")
    point = (0, 1)
    base = (BASE_X, BASE_Y)
    for scalar in range(1, args.count + 1):
        point = add(point, base)
        print(scalar, compress(point))


if __name__ == "__main__":
    main()
