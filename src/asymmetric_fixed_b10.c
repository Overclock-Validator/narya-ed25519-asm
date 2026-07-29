/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Merged cold double-scalar schedule for [s]B-[k]A.
 *
 * The variable point A keeps its balanced radix-32 representation: 51
 * digits and 250 dependent doublings. The immutable generator B uses 26
 * balanced radix-1024 digits. Both digit streams are injected into the one
 * 250-doubling chain, so the B side adds no doublings and needs at most 26
 * affine-Niels additions. This is a scheduling change, not aggregate batch
 * verification: every ZMM lane retains its own s, k, A, accumulator and
 * verdict equation.
 *
 * See docs/architecture/ASYMMETRIC_FIXED_B10.md for the exact integer proof,
 * table provenance, event order, and audit boundary.
 */
#include "internal.h"

#include <string.h>

enum { b10_rounds = 26, b10_entries = 512 };

typedef struct b10_round_x8 {
    uint16_t magnitude[8];
    uint8_t nonzero_mask;
    uint8_t negative_mask;
} b10_round_x8;

typedef struct b10_digits_x8 {
    b10_round_x8 round[b10_rounds];
    uint8_t valid_mask;
} b10_digits_x8;

static const narya_affine_niels_micro_entry_x8 identity_entry = {
    .limb = {{1, 1, 0}},
};

static uint64_t
load_le64(const uint8_t input[8])
{
    uint64_t value = 0;
    for (size_t byte = 0; byte < 8; byte++)
        value |= (uint64_t)input[byte] << (8 * byte);
    return value;
}

static uint16_t
word_bits(const uint64_t words[5], size_t bit)
{
    const size_t word = bit >> 6;
    const unsigned int shift = (unsigned int)(bit & 63);
    uint64_t value = words[word] >> shift;
    if (shift > 54)
        value |= words[word + 1] << (64 - shift);
    return (uint16_t)(value & UINT64_C(1023));
}

static uint8_t
recode_b10(b10_digits_x8 *out, const uint8_t scalar[8 * 32], uint8_t active)
{
    memset(out, 0, sizeof(*out));
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = (uint8_t)(UINT8_C(1) << lane);
        if ((active & lane_mask) == 0 ||
            !narya_scalar_is_canonical(&scalar[lane * 32]))
            continue;

        uint64_t words[5] = {0};
        for (size_t word = 0; word < 4; word++)
            words[word] = load_le64(&scalar[lane * 32 + word * 8]);

        out->valid_mask |= lane_mask;
        int carry = 0;
        for (size_t round = 0; round < b10_rounds; round++) {
            int digit = (int)word_bits(words, round * 10) + carry;
            /* digit+512 is nonnegative; shift is exact division by 1024. */
            carry = (digit + 512) >> 10;
            digit -= carry << 10;
            if (digit != 0) {
                b10_round_x8 *record = &out->round[round];
                record->nonzero_mask |= lane_mask;
                if (digit < 0) {
                    record->negative_mask |= lane_mask;
                    digit = -digit;
                }
                record->magnitude[lane] = (uint16_t)digit;
            }
        }
        /* Canonical scalars are below 2^253; 260 bits absorb the last carry. */
        if (carry != 0)
            return 0;
    }
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
select_b10(
    narya_affine_niels_x8 *out,
    const b10_round_x8 *round,
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
            /* Recode proves every nonzero magnitude lies in 1..512. */
            source[lane] = &narya_fixed_base_b10[magnitude - 1][sign];
        }
    }
    narya_affine_niels_transpose_x8_asm(out, source);
}

static void
double_five(narya_edwards_point_x8 *point)
{
    narya_projective_point_x8 projective;
    narya_edwards_double_to_projective_x8(&projective, point);
    for (size_t doubling = 1; doubling < 4; doubling++)
        narya_projective_double_x8(&projective, &projective);
    narya_projective_double_to_edwards_x8(point, &projective);
}

uint8_t
narya_asymmetric_fixed_b10_double_scalar_mult_x8(
    narya_edwards_point_x8 *out,
    const narya_projective_niels_presigned_table_x8 *variable_table,
    const uint8_t s[8 * 32],
    const uint8_t k[8 * 32],
    uint8_t active)
{
    narya_radix32_digits_x8 a_digits;
    uint8_t valid = narya_scalar_recode_radix32_x8(
        &a_digits, k, active, active);
    b10_digits_x8 b_digits;
    valid &= recode_b10(&b_digits, s, active);

    narya_edwards_point_x8 accumulator;
    set_identity(&accumulator);
    if (valid == 0) {
        *out = accumulator;
        return 0;
    }

    for (int block = b10_rounds - 1; block >= 0; block--) {
        const b10_round_x8 *b_round = &b_digits.round[(size_t)block];
        if ((b_round->nonzero_mask & valid) != 0) {
            narya_affine_niels_x8 selected;
            select_b10(&selected, b_round, valid);
            narya_edwards_add_affine_niels_x8(
                &accumulator, &accumulator, &selected);
        }

        const narya_radix32_round_x8 *a_even =
            &a_digits.round[(size_t)block * 2];
        if ((a_even->nonzero_mask & valid) != 0) {
            narya_projective_niels_x8 selected;
            narya_projective_niels_table_select_x8(
                &selected, variable_table, a_even, valid);
            narya_edwards_add_projective_niels_x8(
                &accumulator, &accumulator, &selected);
        }
        if (block == 0)
            break;

        double_five(&accumulator);
        const narya_radix32_round_x8 *a_odd =
            &a_digits.round[(size_t)block * 2 - 1];
        if ((a_odd->nonzero_mask & valid) != 0) {
            narya_projective_niels_x8 selected;
            narya_projective_niels_table_select_x8(
                &selected, variable_table, a_odd, valid);
            narya_edwards_add_projective_niels_x8(
                &accumulator, &accumulator, &selected);
        }
        double_five(&accumulator);
    }
    *out = accumulator;
    return valid;
}
