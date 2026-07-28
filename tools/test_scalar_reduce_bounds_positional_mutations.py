#!/usr/bin/env python3
"""Require the scalar source certificate to reject semantic route drift.

The interval bounds alone cannot detect every arithmetic error: swapping two
equally bounded fold targets, redirecting a carry, or deleting the rounded-
carry constant load can remain range-safe while changing the represented
integer. Each disposable mutation below must therefore fail the checker.
"""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src" / "scalar_reduce_x8.S"
CHECKER = ROOT / "tools" / "check_scalar_reduce_bounds.py"

MUTATIONS = {
    "swap_fold_targets": (
        "FOLD zmm23, zmm11, zmm12, zmm13, zmm14, zmm15, zmm16",
        "FOLD zmm23, zmm12, zmm11, zmm13, zmm14, zmm15, zmm16",
    ),
    "misroute_centered_carry": (
        "CARRY_ROUNDED zmm6,  zmm7",
        "CARRY_ROUNDED zmm6,  zmm0",
    ),
    "delete_round_broadcast": (
        "    vpbroadcastq zmm31, QWORD PTR [rip + .Lscalar_round]\n",
        "",
    ),
}


def mutation_is_rejected(name: str, old: str, new: str) -> bool:
    with tempfile.TemporaryDirectory(prefix="narya-scalar-mutation-") as directory:
        root = Path(directory)
        (root / "src").mkdir()
        (root / "tools").mkdir()

        source = SOURCE.read_text(encoding="ascii")
        if source.count(old) < 1:
            raise RuntimeError(f"{name}: source pattern was not found")
        (root / "src" / SOURCE.name).write_text(
            source.replace(old, new, 1), encoding="ascii"
        )
        (root / "tools" / CHECKER.name).write_text(
            CHECKER.read_text(encoding="utf-8"), encoding="utf-8"
        )

        result = subprocess.run(
            ["python3", str(root / "tools" / CHECKER.name)],
            cwd=root,
            text=True,
            capture_output=True,
        )
        if result.returncode == 0:
            print(f"FAIL: {name} was accepted")
            if result.stdout:
                print(result.stdout, end="")
            return False
        print(f"PASS: {name} was rejected")
        return True


def main() -> None:
    accepted = [
        name
        for name, (old, new) in MUTATIONS.items()
        if not mutation_is_rejected(name, old, new)
    ]
    if accepted:
        raise SystemExit(
            "scalar certificate accepted arithmetic-breaking mutations: "
            + ", ".join(accepted)
        )
    print("PASS: every scalar positional/constant-load mutation was rejected")


if __name__ == "__main__":
    main()
