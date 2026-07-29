#!/usr/bin/env python3
"""Require representative r51 linear-leaf mutations to fail certification."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/r51x8_ifma.S"
GENERATOR = ROOT / "tools/generate_r51_linear_trace.py"


MUTATIONS = {
    "add-opcode": (
        "vpaddq zmm0, zmm0, ZMMWORD PTR [rdx +   0]",
        "vpsubq zmm0, zmm0, ZMMWORD PTR [rdx +   0]",
    ),
    "add-input-offset": (
        "vpaddq zmm1, zmm1, ZMMWORD PTR [rdx +  64]",
        "vpaddq zmm1, zmm1, ZMMWORD PTR [rdx + 128]",
    ),
    "subtract-bias-limb": (
        "vpaddq zmm0, zmm0, zmm9",
        "vpaddq zmm0, zmm0, zmm10",
    ),
    "subtract-opcode": (
        "vpsubq zmm4, zmm4, ZMMWORD PTR [rdx + 256]",
        "vpaddq zmm4, zmm4, ZMMWORD PTR [rdx + 256]",
    ),
    "negate-source-offset": (
        "vpsubq zmm3, zmm3, ZMMWORD PTR [rsi + 192]",
        "vpsubq zmm3, zmm3, ZMMWORD PTR [rsi + 256]",
    ),
    "normalize-register": (
        "NORMALIZE_5 zmm0, zmm1",
        "NORMALIZE_5 zmm1, zmm0",
    ),
    "output-limb": (
        "vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2",
        "vmovdqu64 ZMMWORD PTR [rdi + 128], zmm3",
    ),
    "bias-constant": (
        "narya_ifma_sub_bias0:\n    .quad 0x001fffffffffffb4",
        "narya_ifma_sub_bias0:\n    .quad 0x001fffffffffffb3",
    ),
    "carry-opcode": (
        r"vpaddq \in4, \in4, \c3",
        r"vpsubq \in4, \in4, \c3",
    ),
}

MUTATION_FUNCTIONS = {
    "add-opcode": "narya_r51x8_add_ifma",
    "add-input-offset": "narya_r51x8_add_ifma",
    "subtract-bias-limb": "narya_r51x8_sub_ifma",
    "subtract-opcode": "narya_r51x8_sub_ifma",
    "negate-source-offset": "narya_r51x8_neg_ifma",
    "normalize-register": "narya_r51x8_add_ifma",
    "output-limb": "narya_r51x8_add_ifma",
}


def function_body_bounds(source: str, function: str) -> tuple[int, int]:
    start_marker = f"\n{function}:\n"
    end_marker = f"\n.size {function},"
    start = source.index(start_marker) + 1
    end = source.index(end_marker, start)
    return start, end


def main() -> None:
    source = SOURCE.read_text(encoding="ascii")
    baseline = subprocess.run(
        [sys.executable, str(GENERATOR), "--check"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if baseline.returncode != 0:
        raise SystemExit("baseline linear trace check failed:\n" + baseline.stderr)

    for name, (old, new) in MUTATIONS.items():
        function = MUTATION_FUNCTIONS.get(name)
        if function is None:
            start, end = 0, len(source)
        else:
            start, end = function_body_bounds(source, function)
        scope = source[start:end]
        count = scope.count(old)
        if count != 1:
            raise SystemExit(
                f"mutation anchor {name!r} occurs {count} times in its audit "
                "scope, expected once"
            )
        mutated = source[:start] + scope.replace(old, new, 1) + source[end:]
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".S", encoding="ascii", delete=False
        ) as temporary:
            temporary.write(mutated)
            path = Path(temporary.name)
        try:
            result = subprocess.run(
                [sys.executable, str(GENERATOR), "--source", str(path), "--check"],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
        finally:
            path.unlink()
        if result.returncode == 0:
            raise SystemExit(f"mutation {name!r} was not detected")
        print(f"OK: mutation {name} is rejected")


if __name__ == "__main__":
    main()
