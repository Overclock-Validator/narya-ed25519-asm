#!/usr/bin/env python3
"""Require the source-to-Lean whole-leaf extractor to fail closed."""
from __future__ import annotations

from dataclasses import dataclass

import generate_transpose_whole_trace as generator


@dataclass(frozen=True)
class Mutation:
    name: str
    target: str
    old: str
    new: str
    occurrence: int = 0


MUTATIONS = (
    Mutation(
        "projective-pointer-assignment",
        "projective",
        "mov rdx, QWORD PTR [rsi + 0]",
        "mov rcx, QWORD PTR [rsi + 0]",
    ),
    Mutation(
        "projective-pointer-table-offset",
        "projective",
        "mov rcx, QWORD PTR [rsi + 8]",
        "mov rcx, QWORD PTR [rsi + 16]",
    ),
    Mutation(
        "affine-mask-immediate",
        "affine",
        "mov eax, 7",
        "mov eax, 15",
    ),
    Mutation(
        "affine-source-offset",
        "affine",
        "TRANSPOSE_HALF 24, 64, rdx, rcx, r8,  r9",
        "TRANSPOSE_HALF 32, 64, rdx, rcx, r8,  r9",
    ),
    Mutation(
        "projective-store-offset",
        "projective",
        r"vmovdqu YMMWORD PTR [rax + 320 + 2*\off + \half], ymm1",
        r"vmovdqu YMMWORD PTR [rax + 328 + 2*\off + \half], ymm1",
    ),
    Mutation(
        "shuffle-immediate",
        "projective",
        "vshufi64x2 ymm2, ymm4, ymm6, 0x03",
        "vshufi64x2 ymm2, ymm4, ymm6, 0x02",
    ),
    Mutation(
        "projective-epilogue",
        "projective",
        "    vzeroupper\n    ret",
        "    ret\n    vzeroupper",
    ),
    Mutation(
        "affine-epilogue",
        "affine",
        "    vzeroupper\n    ret",
        "    vzeroupper\n    nop\n    ret",
    ),
)


def replace_nth(text: str, old: str, new: str, occurrence: int) -> str:
    start = 0
    found = -1
    for _ in range(occurrence + 1):
        found = text.find(old, start)
        if found < 0:
            raise SystemExit(f"mutation anchor not found: {old!r}")
        start = found + len(old)
    return text[:found] + new + text[found + len(old):]


def main() -> None:
    projective = generator.PROJECTIVE_SOURCE.read_text(encoding="ascii")
    affine = generator.AFFINE_SOURCE.read_text(encoding="ascii")
    generator.validate_source_texts(projective, affine)
    for mutation in MUTATIONS:
        ptext, atext = projective, affine
        if mutation.target == "projective":
            ptext = replace_nth(ptext, mutation.old, mutation.new, mutation.occurrence)
        else:
            atext = replace_nth(atext, mutation.old, mutation.new, mutation.occurrence)
        try:
            generator.validate_source_texts(ptext, atext)
        except SystemExit as error:
            print(f"OK: source mutation {mutation.name} rejected: {error}")
            continue
        raise SystemExit(f"source mutation {mutation.name!r} was not detected")
    print(f"PASS: all {len(MUTATIONS)} source whole-leaf mutations were rejected")


if __name__ == "__main__":
    main()
