/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Two-way radix-256 comb for the immutable Ed25519 basepoint.
 * See docs/architecture/FIXED_BASE_COMB.md for the integer decomposition and
 * data provenance. Public digits permit direct indexing; no secret scalar is
 * processed by this verification-only library.
 */
#include "internal.h"

#include <string.h>

enum { comb_rounds = 32, comb_positions = 16, comb_entries = 128 };

typedef struct comb_digits_x8 {
    narya_radix32_round_x8 round[comb_rounds];
    uint8_t valid_mask;
} comb_digits_x8;

static const narya_affine_niels_micro_entry_x8 identity_entry = {
    .limb = {{1, 1, 0}},
};

static uint8_t
recode(comb_digits_x8 *out, const uint8_t scalar[8 * 32], uint8_t active)
{
    memset(out, 0, sizeof(*out));
    int carry[8] = {0};
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = (uint8_t)(UINT8_C(1) << lane);
        if ((active & lane_mask) != 0 &&
            narya_scalar_is_canonical(&scalar[lane * 32]))
            out->valid_mask |= lane_mask;
    }

    for (size_t round = 0; round < comb_rounds; round++) {
        narya_radix32_round_x8 *digit_round = &out->round[round];
        for (size_t lane = 0; lane < 8; lane++) {
            const uint8_t lane_mask = (uint8_t)(UINT8_C(1) << lane);
            if ((out->valid_mask & lane_mask) == 0)
                continue;
            int digit = (int)scalar[lane * 32 + round] + carry[lane];
            carry[lane] = (digit + 128) / 256;
            digit -= carry[lane] * 256;
            if (digit != 0) {
                digit_round->nonzero_mask |= lane_mask;
                if (digit < 0) {
                    digit_round->negative_mask |= lane_mask;
                    digit = -digit;
                }
                digit_round->magnitude[lane] = (uint8_t)digit;
            }
        }
    }
    for (size_t lane = 0; lane < 8; lane++)
        if (carry[lane] != 0)
            return 0;
    return out->valid_mask;
}

static void
set_identity(narya_edwards_point_x8 *point)
{
    *point = (narya_edwards_point_x8){0};
    for (size_t lane = 0; lane < 8; lane++) {
        point->Y.limb[0][lane] = 1;
        point->Z.limb[0][lane] = 1;
    }
}

static void
select_entry(
    narya_affine_niels_x8 *out,
    size_t position,
    const narya_radix32_round_x8 *round,
    uint8_t active)
{
    const uint8_t lookup = round->nonzero_mask & active;
    const narya_affine_niels_micro_entry_x8 *source[8];
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = (uint8_t)(UINT8_C(1) << lane);
        source[lane] = &identity_entry;
        if ((lookup & lane_mask) != 0) {
            const size_t magnitude = round->magnitude[lane];
            const size_t sign = (round->negative_mask >> lane) & 1U;
            /* Recode proves magnitude in 1..128 for every nonzero lane. */
            source[lane] =
                &narya_fixed_base_comb_r256[position][magnitude - 1][sign];
        }
    }
    narya_affine_niels_transpose_x8_asm(out, source);
}

uint8_t
narya_fixed_base_scalar_mult_x8(
    narya_edwards_point_x8 *out,
    const uint8_t scalar[8 * 32],
    uint8_t active)
{
    comb_digits_x8 digits;
    const uint8_t valid = recode(&digits, scalar, active);
    narya_edwards_point_x8 accumulator;
    set_identity(&accumulator);
    if (valid == 0) {
        *out = accumulator;
        return 0;
    }

    /* Odd columns, multiply by 2^8, then even columns. */
    for (size_t position = 0; position < comb_positions; position++) {
        const narya_radix32_round_x8 *round = &digits.round[2 * position + 1];
        if ((round->nonzero_mask & valid) != 0) {
            narya_affine_niels_x8 selected;
            select_entry(&selected, position, round, valid);
            narya_edwards_add_affine_niels_x8(
                &accumulator, &accumulator, &selected);
        }
    }
    for (size_t doubling = 0; doubling < 8; doubling++)
        narya_edwards_double_x8(&accumulator, &accumulator);
    for (size_t position = 0; position < comb_positions; position++) {
        const narya_radix32_round_x8 *round = &digits.round[2 * position];
        if ((round->nonzero_mask & valid) != 0) {
            narya_affine_niels_x8 selected;
            select_entry(&selected, position, round, valid);
            narya_edwards_add_affine_niels_x8(
                &accumulator, &accumulator, &selected);
        }
    }
    *out = accumulator;
    return valid;
}
