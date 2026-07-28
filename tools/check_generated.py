#!/usr/bin/env python3
"""Rebuild committed deterministic artifacts and require byte equality."""

from __future__ import annotations

import difflib
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def run(*arguments: str) -> bytes:
    return subprocess.run(
        [sys.executable, *arguments],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def require_equal(path: Path, generated: bytes) -> None:
    committed = path.read_bytes()
    if committed == generated:
        print(f"OK: {path.relative_to(ROOT)}")
        return

    print(f"generated artifact differs: {path.relative_to(ROOT)}", file=sys.stderr)
    if path.suffix != ".bin":
        before = committed.decode("ascii").splitlines(keepends=True)
        after = generated.decode("ascii").splitlines(keepends=True)
        sys.stderr.writelines(
            difflib.unified_diff(before, after, fromfile="committed", tofile="generated")
        )
    raise SystemExit(1)


def main() -> None:
    require_equal(
        ROOT / "formal/lean/NaryaFormal/GeneratedR51MulTrace.lean",
        run("tools/generate_r51_mul_trace.py"),
    )
    require_equal(
        ROOT / "formal/lean/NaryaFormal/GeneratedR51LinearTrace.lean",
        run("tools/generate_r51_linear_trace.py"),
    )
    require_equal(
        ROOT / "formal/lean/NaryaFormal/GeneratedR51InstructionTrace.lean",
        run("tools/generate_r51_instruction_trace.py"),
    )

    external = ROOT / "tests/vectors/narya_external_strict_v1.jsonl"
    external_sha256 = hashlib.sha256(external.read_bytes()).hexdigest()
    expected_external_sha256 = (
        "c18c229799ba137dc04377ccdcb173646f8e533d528b5433e40310737605bd38"
    )
    if external_sha256 != expected_external_sha256:
        raise SystemExit(
            "external corpus changed without a provenance update: "
            f"{external_sha256} != {expected_external_sha256}"
        )
    print("OK: tests/vectors/narya_external_strict_v1.jsonl (pinned SHA-256)")

    require_equal(
        ROOT / "tests/vectors/narya_basepoint_multiples_v1.txt",
        run("tools/generate_basepoint_multiples.py", "-count", "128"),
    )
    require_equal(
        ROOT / "tests/vectors/narya_variable_scalar_mult_v1.txt",
        run("tools/generate_variable_scalar_vectors.py", "-groups", "32"),
    )

    with tempfile.TemporaryDirectory(prefix="narya-generated-") as temporary:
        directory = Path(temporary)

        strict = directory / "strict.txt"
        run("tools/generate_strict_verify_vectors.py", "--output", str(strict))
        require_equal(
            ROOT / "tests/vectors/narya_strict_verify_v1.txt", strict.read_bytes()
        )

        table = directory / "comb.bin"
        vectors = directory / "comb.txt"
        run(
            "tools/generate_fixed_base_comb.py",
            "--table",
            str(table),
            "--vectors",
            str(vectors),
            "--groups",
            "32",
        )
        require_equal(ROOT / "data/narya_fixed_base_comb_r256.bin", table.read_bytes())
        require_equal(
            ROOT / "tests/vectors/narya_fixed_base_scalar_v1.txt",
            vectors.read_bytes(),
        )

        fuzz = directory / "fuzz"
        run(
            "tools/generate_fuzz_seeds.py",
            "--corpus",
            str(external),
            "--output-dir",
            str(fuzz),
        )
        for name in (
            "accepted-x8",
            "rejected-x8",
            "predicate-edges-x8",
            "partial-mixed-x4",
        ):
            require_equal(
                ROOT / "tests/fuzz/corpus/verify_strict_x8" / name,
                (fuzz / name).read_bytes(),
            )


if __name__ == "__main__":
    main()
