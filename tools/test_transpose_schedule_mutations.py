#!/usr/bin/env python3
"""Require the x8 transpose source certificate to reject schedule mutations."""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import check_transpose_schedule as checker  # noqa: E402


PROJECTIVE = (ROOT / "src/projective_niels_transpose_x8.S").read_text(
    encoding="ascii"
)
AFFINE = (ROOT / "src/affine_niels_transpose_x8.S").read_text(encoding="ascii")


MUTATIONS = (
    (
        "projective-shuffle-immediate",
        checker.certify_projective,
        PROJECTIVE,
        "vshufi64x2 ymm2, ymm4, ymm6, 0x03",
        "vshufi64x2 ymm2, ymm4, ymm6, 0x01",
    ),
    (
        "projective-lane-half-offset",
        checker.certify_projective,
        PROJECTIVE,
        "TRANSPOSE_HALF 0,  32, r10, r11, rdi, rsi",
        "TRANSPOSE_HALF 0,  24, r10, r11, rdi, rsi",
    ),
    (
        "projective-inserted-instruction",
        checker.certify_projective,
        PROJECTIVE,
        "    TRANSPOSE_HALF 0,   0, rdx, rcx, r8,  r9",
        "    xor eax, eax\n    TRANSPOSE_HALF 0,   0, rdx, rcx, r8,  r9",
    ),
    (
        "projective-pointer-map",
        checker.certify_projective,
        PROJECTIVE,
        "mov rdi, QWORD PTR [rsi + 48]",
        "mov rdi, QWORD PTR [rsi + 56]",
    ),
    (
        "affine-mask",
        checker.certify_affine,
        AFFINE,
        "mov eax, 7",
        "mov eax, 15",
    ),
    (
        "affine-masked-load",
        checker.certify_affine,
        AFFINE,
        r"vmovdqu64 ymm0{k1}{z}, YMMWORD PTR [\p0 + \source_offset]",
        r"vmovdqu64 ymm0, YMMWORD PTR [\p0 + \source_offset]",
    ),
    (
        "affine-output-offset",
        checker.certify_affine,
        AFFINE,
        "TRANSPOSE_HALF 96, 288, r10, r11, rdi, rsi",
        "TRANSPOSE_HALF 96, 280, r10, r11, rdi, rsi",
    ),
    (
        "affine-inserted-instruction",
        checker.certify_affine,
        AFFINE,
        "    TRANSPOSE_HALF 0,   0, rdx, rcx, r8,  r9",
        "    xor eax, eax\n    TRANSPOSE_HALF 0,   0, rdx, rcx, r8,  r9",
    ),
)


def main() -> None:
    checker.certify_projective(PROJECTIVE)
    checker.certify_affine(AFFINE)
    for name, certify, source, old, new in MUTATIONS:
        if source.count(old) != 1:
            raise SystemExit(
                f"mutation anchor {name!r} occurs {source.count(old)} times, expected once"
            )
        try:
            certify(source.replace(old, new, 1))
        except AssertionError:
            print(f"OK: mutation {name} is rejected")
            continue
        raise SystemExit(f"mutation {name!r} was not detected")


if __name__ == "__main__":
    main()
