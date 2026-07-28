#!/usr/bin/env python3
"""Generate deterministic libFuzzer seeds from the committed external corpus."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


LANES = 8


def encode(active: int, cases: list[dict[str, object]]) -> bytes:
    cases = list(cases)
    zero = {"public_key": "00" * 32, "signature": "00" * 64, "message": ""}
    cases.extend([zero] * (LANES - len(cases)))
    header = bytearray([active])
    header.extend(b"".join(bytes.fromhex(str(item["public_key"])) for item in cases))
    header.extend(b"".join(bytes.fromhex(str(item["signature"])) for item in cases))
    messages = [bytes.fromhex(str(item["message"])) for item in cases]
    for message in messages:
        header.extend(len(message).to_bytes(2, "little"))
    for message in messages:
        header.extend(message)
    return bytes(header)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    records = [json.loads(line) for line in args.corpus.read_text().splitlines()]
    by_prefix: dict[str, list[dict[str, object]]] = {}
    for item in records:
        by_prefix.setdefault(str(item["name"]).split("/")[0], []).append(item)

    accepted = [item for item in records if item["narya_dalek_strict"]]
    rejected = [item for item in records if not item["narya_dalek_strict"]]
    seeds = {
        "accepted-x8": encode(0xFF, accepted[:LANES]),
        "rejected-x8": encode(0xFF, rejected[:LANES]),
        "predicate-edges-x8": encode(
            0xFF,
            by_prefix["small-order"][:4] + by_prefix["noncanonical-y"][:4],
        ),
        "partial-mixed-x4": encode(0x0F, [accepted[0], rejected[0], accepted[1], rejected[1]]),
    }

    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, seed in seeds.items():
        (args.output_dir / name).write_bytes(seed)


if __name__ == "__main__":
    main()
