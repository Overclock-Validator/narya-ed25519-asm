#!/usr/bin/env python3
"""Generate one independent heterogeneous x8 Ed25519 verification group."""

import argparse
import hashlib
from pathlib import Path

from generate_basepoint_multiples import BASE_X, BASE_Y, add, compress

L = 2**252 + 27742317777372353535851937790883648493
LENGTHS = [0, 1, 17, 64, 200, 1232, 4096, 511]


def scalar_mult(scalar, point):
    result = (0, 1)
    addend = point
    while scalar:
        if scalar & 1:
            result = add(result, addend)
        addend = add(addend, addend)
        scalar >>= 1
    return result


def sign(seed, message):
    digest = hashlib.sha512(seed).digest()
    secret = bytearray(digest[:32])
    secret[0] &= 248
    secret[31] &= 63
    secret[31] |= 64
    scalar = int.from_bytes(secret, "little")
    public = bytes.fromhex(compress(scalar_mult(scalar, (BASE_X, BASE_Y))))
    nonce = int.from_bytes(hashlib.sha512(digest[32:] + message).digest(), "little") % L
    r_encoded = bytes.fromhex(compress(scalar_mult(nonce, (BASE_X, BASE_Y))))
    challenge = int.from_bytes(
        hashlib.sha512(r_encoded + public + message).digest(), "little"
    ) % L
    s = (nonce + challenge * scalar) % L
    return public, r_encoded + s.to_bytes(32, "little")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    lines = [
        "# narya-strict-verify-v1",
        "# lane public_key_hex signature_hex message_hex_or_dash",
    ]
    for lane, length in enumerate(LENGTHS):
        seed = hashlib.sha512(f"narya-asm-seed-{lane}".encode()).digest()[:32]
        message = bytes((lane * 29 + index * 17 + 3) & 0xFF for index in range(length))
        public, signature = sign(seed, message)
        lines.append(
            f"{lane} {public.hex()} {signature.hex()} "
            f"{message.hex() if message else '-'}"
        )
    text = "\n".join(lines) + "\n"
    if args.output is None:
        print(text, end="")
    else:
        args.output.write_text(text, encoding="ascii")


if __name__ == "__main__":
    main()
