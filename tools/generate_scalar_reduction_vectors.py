#!/usr/bin/env python3
"""Generate deterministic adversarial vectors for scalar reduction.

Expected values use Python's independent arbitrary-precision `% L`; the
generator does not reproduce the assembly's radix folds, carries, or packer.
"""

from __future__ import annotations

import json


B = 1 << 21
L = (1 << 252) + 27742317777372353535851937790883648493
INPUT_BYTES = 64
OUTPUT_BYTES = 32


def radix_value(digits: dict[int, int]) -> int:
    return sum(digit * B**position for position, digit in digits.items())


def vector(label: str, purpose: str, value: int) -> dict[str, str]:
    if not 0 <= value < 1 << 512:
        raise ValueError(f"{label}: input is not a 512-bit unsigned integer")
    expected = value % L
    return {
        "label": label,
        "purpose": purpose,
        "input_integer_decimal": str(value),
        "input_64_le_hex": value.to_bytes(INPUT_BYTES, "little").hex(),
        "expected_integer_decimal": str(expected),
        "expected_32_le_hex": expected.to_bytes(OUTPUT_BYTES, "little").hex(),
    }


def lane(lane_index: int, item: dict[str, str]) -> dict[str, str | int]:
    return {
        "lane": lane_index,
        "label": item["label"],
        "input_64_le_hex": item["input_64_le_hex"],
        "expected_32_le_hex": item["expected_32_le_hex"],
    }


def build_vectors() -> list[dict[str, str]]:
    specs = [
        ("zero", "all paths at zero", 0),
        ("one", "least nonzero residue", 1),
        (
            "centered_carry_just_below",
            "CARRY_ROUNDED must choose q=0 and residual 2^20-1",
            (1 << 20) - 1,
        ),
        (
            "centered_carry_boundary",
            "CARRY_ROUNDED must choose q=1 and residual -2^20",
            1 << 20,
        ),
        (
            "negative_ordinary_carry_witness",
            "the preceding rounded carry creates -1; VPSRAQ must produce "
            "ordinary quotient -1",
            B - 1,
        ),
        ("radix_B", "adjacent-limb reconstruction", B),
        ("two252_minus_1", "top ordinary 252-bit boundary", (1 << 252) - 1),
        ("two252", "fold relation at B^12", 1 << 252),
        (
            "L_minus_1",
            "largest canonical scalar; output bit 252 must survive",
            L - 1,
        ),
        ("L", "must reduce to canonical zero", L),
        ("L_plus_1", "must reduce to canonical one", L + 1),
        ("twoL_minus_1", "large congruent canonical boundary", 2 * L - 1),
        ("twoL", "must reduce to canonical zero", 2 * L),
        (
            "all_ones_512",
            "all parser limbs maximal and long carry/fold stress",
            (1 << 512) - 1,
        ),
    ]

    vectors = [vector(*spec) for spec in specs]
    for position in range(12, 24):
        maximum = (1 << 29) - 1 if position == 23 else B - 1
        vectors.append(
            vector(
                f"isolated_max_limb_{position}",
                f"isolates FOLD source limb {position}",
                radix_value({position: maximum}),
            )
        )

    vectors.extend(
        [
            vector(
                "widest_interval_negative_witness",
                "attains -537126723016406 at subtraction of 683901*zmm21 "
                "from zmm14",
                radix_value({21: B - 1, 23: (1 << 29) - 1}),
            ),
            vector(
                "same_instruction_positive_endpoint_witness",
                "attains 286592461358 at the same zmm14 update",
                radix_value({14: B - 1, 22: B - 1}),
            ),
            vector(
                "all_digits_centered_just_below",
                "many rounded carries remain at the lower quotient side",
                radix_value({position: (1 << 20) - 1 for position in range(24)}),
            ),
            vector(
                "all_digits_centered_boundary",
                "many rounded carries cross the exact +2^20 threshold",
                radix_value({position: 1 << 20 for position in range(24)}),
            ),
            vector(
                "alternating_max_zero_digits",
                "stresses alternating carry waves and omitted-neighbor errors",
                radix_value({position: B - 1 for position in range(0, 23, 2)}),
            ),
        ]
    )
    return vectors


def main() -> None:
    vectors = build_vectors()
    by_label = {item["label"]: item for item in vectors}
    bundle_labels = [
        "zero",
        "all_ones_512",
        "L_minus_1",
        "L",
        "two252",
        "widest_interval_negative_witness",
        "same_instruction_positive_endpoint_witness",
        "negative_ordinary_carry_witness",
    ]
    document = {
        "schema": "narya.scalar-reduction-adversarial-v1",
        "B": str(B),
        "L": str(L),
        "vectors": vectors,
        "x8_lane_bundle": {
            "description": (
                "Eight deliberately distinct lanes for lane-mixing and "
                "active-mask tests"
            ),
            "lanes": [
                lane(index, by_label[label])
                for index, label in enumerate(bundle_labels)
            ],
            "recommended_active_masks_hex": ["00", "01", "55", "aa", "ff"],
        },
    }
    print(json.dumps(document, indent=2))


if __name__ == "__main__":
    main()
