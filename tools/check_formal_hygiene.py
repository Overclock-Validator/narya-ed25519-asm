#!/usr/bin/env python3
"""Fail closed on common Lean audit-hygiene regressions.

This checker does not decide whether a theorem is mathematically meaningful;
Lean's kernel and human review do that. It keeps the review boundary honest by
rejecting proof placeholders and requiring the named audit anchors documented
in docs/proofs/FORMAL_EVIDENCE_INDEX.md to remain real declarations.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "formal/lean/NaryaFormal"

FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|sorryAx)\b")

# Stable entry points for an auditor. Renaming or moving one requires an
# intentional evidence-index update.
AUDIT_ANCHORS = {
    "AssemblyTrace.lean": ("radix51_mul_assembly_trace_correct",),
    "LinearTrace.lean": (
        "add_assembly_trace_correct",
        "sub_assembly_trace_correct",
        "neg_assembly_trace_correct",
    ),
    "X86ObjectRefinement.lean": (
        "r51_object_decodes_to_source_instruction_trace",
    ),
    "X86NatShadow.lean": ("runR51NatShadow_correct",),
    "X86Refinement.lean": ("run_arithmetic_core_refines",),
    "X86Noninterference.lean": (
        "run_arithmetic_core_ignores_undefined_scratch",
    ),
    "X86InputRefinement.lean": ("run_prepare_phase",),
    "X86MemoryRefinement.lean": ("run_store_phase_refines",),
    "X86BodyRefinement.lean": ("run_decoded_body_refines",),
    "X86EpilogueRefinement.lean": (
        "run_expected_program_after_body",
        "run_r51_multiplier_refines",
    ),
    "X86Dataflow.lean": (
        "decoded_body_definite_assignment",
        "arithmetic_core_definite_assignment",
    ),
    "Transpose.lean": (
        "projective_transpose_x8_lane_exact",
        "affine_transpose_x8_lane_exact",
    ),
    "ScalarReduction.lean": (
        "fold_polynomial_exact",
        "radix12_fold_mod_order",
    ),
    "VerificationSpine.lean": (
        "verifyStrict_correct",
        "verifyStrictX8_correct",
    ),
}


def declaration_exists(source: str, name: str) -> bool:
    pattern = rf"(?m)^\s*(?:theorem|lemma)\s+{re.escape(name)}(?:\s|\[|\()"
    return re.search(pattern, source) is not None


def code_without_comments(source: str) -> str:
    """Remove Lean line and nested block comments while preserving newlines."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if not in_string and pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
            continue
        if not in_string and pair == "--":
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
            continue
        if char == '"' and (index == 0 or source[index - 1] != "\\"):
            in_string = not in_string
        output.append(char)
        index += 1
    return "".join(output)


def main() -> None:
    failures: list[str] = []

    project_sources = [LEAN_ROOT.parent / "NaryaFormal.lean"]
    project_sources.extend(sorted(LEAN_ROOT.rglob("*.lean")))
    for path in project_sources:
        source = path.read_text(encoding="utf-8")
        code = code_without_comments(source)
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            failures.append(
                f"{path.relative_to(ROOT)}:{line}: forbidden proof escape "
                f"{match.group(0)!r}"
            )

    for filename, names in AUDIT_ANCHORS.items():
        path = LEAN_ROOT / filename
        if not path.is_file():
            failures.append(f"missing audit module: {path.relative_to(ROOT)}")
            continue
        source = path.read_text(encoding="utf-8")
        for name in names:
            if not declaration_exists(source, name):
                failures.append(
                    f"{path.relative_to(ROOT)}: missing audit anchor {name}"
                )

    if failures:
        raise SystemExit("\n".join(failures))

    anchor_count = sum(len(names) for names in AUDIT_ANCHORS.values())
    print(
        f"OK: no Lean proof escapes; {anchor_count} audit anchors are present "
        f"in {len(AUDIT_ANCHORS)} modules"
    )


if __name__ == "__main__":
    main()
