#!/usr/bin/env python3
"""Prove that representative r51 assembly mutations break trace checking."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/r51x8_ifma.S"
GENERATOR = ROOT / "tools/generate_r51_mul_trace.py"


MUTATIONS = {
    "accumulator-clear": (
        r"vpxorq \r, \r, \r",
        r"vpandq \r, \r, \r",
    ),
    "low-accumulator-target": (
        "MUL_PAIR zmm0, zmm5, zmm10, zmm19",
        "MUL_PAIR zmm0, zmm5, zmm11, zmm19",
    ),
    "missing-product": (
        "    MUL_PAIR zmm4, zmm9, zmm18, zmm27\n",
        "",
    ),
    "combine-target": (
        "COMBINE_HIGH zmm19, zmm11",
        "COMBINE_HIGH zmm19, zmm12",
    ),
    "fold-source": (
        "FOLD_INTO zmm10, zmm15, zmm28, zmm30",
        "FOLD_INTO zmm10, zmm16, zmm28, zmm30",
    ),
    "fold-constant": (
        "narya_ifma_fold19:\n    .quad 19",
        "narya_ifma_fold19:\n    .quad 17",
    ),
    "normalize-input-order": (
        "NORMALIZE_5 zmm10, zmm11, zmm12, zmm13, zmm14, zmm5",
        "NORMALIZE_5 zmm11, zmm10, zmm12, zmm13, zmm14, zmm5",
    ),
    "output-lane-order": (
        "vmovdqu64 ZMMWORD PTR [rdi +   0], zmm10",
        "vmovdqu64 ZMMWORD PTR [rdi +   0], zmm11",
    ),
    "ifma-opcode": (
        r"vpmadd52luq \l, \x, \y",
        r"vpmadd52huq \l, \x, \y",
    ),
    "unmodeled-instruction": (
        "    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm14\n    vzeroupper",
        "    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm14\n"
        "    vpaddq zmm10, zmm10, zmm11\n    vzeroupper",
    ),
    "source-load-offset": (
        "/* Load all sources first: this is the alias-safety proof boundary. */\n"
        "    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]",
        "/* Load all sources first: this is the alias-safety proof boundary. */\n"
        "    vmovdqu64 zmm0, ZMMWORD PTR [rsi +  64]",
    ),
}

GLOBAL_MUTATIONS = {"accumulator-clear", "fold-constant", "ifma-opcode"}


def mul_body_bounds(source: str) -> tuple[int, int]:
    start_marker = "\nnarya_r51x8_mul_ifma:\n"
    end_marker = "\n.size narya_r51x8_mul_ifma,"
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
        raise SystemExit("baseline trace check failed:\n" + baseline.stderr)

    for name, (old, new) in MUTATIONS.items():
        if name in GLOBAL_MUTATIONS:
            start, end = 0, len(source)
        else:
            start, end = mul_body_bounds(source)
        scope = source[start:end]
        if scope.count(old) != 1:
            raise SystemExit(
                f"mutation anchor {name!r} occurs {scope.count(old)} times "
                "in its audit scope, expected once"
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
