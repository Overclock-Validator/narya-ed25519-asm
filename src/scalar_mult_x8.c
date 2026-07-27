/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

static void
set_identity(narya_edwards_point_x8 *point)
{
    *point = (narya_edwards_point_x8){0};
    for (size_t lane = 0; lane < 8; lane++) {
        point->Y.limb[0][lane] = 1;
        point->Z.limb[0][lane] = 1;
    }
}

uint8_t
narya_variable_scalar_mult_x8(
    narya_edwards_point_x8 *out,
    const narya_projective_niels_presigned_table_x8 *table,
    const uint8_t scalar[8 * 32],
    uint8_t negative_mask,
    uint8_t active)
{
    narya_radix32_digits_x8 digits;
    const uint8_t valid = narya_scalar_recode_radix32_x8(
        &digits, scalar, negative_mask, active);
    narya_edwards_point_x8 accumulator;
    set_identity(&accumulator);
    if (valid == 0) {
        *out = accumulator;
        return 0;
    }

    /* Horner evaluation of the exact signed radix-32 expansion. */
    for (size_t round = NARYA_RADIX32_ROUNDS; round-- > 0;) {
        if (round != NARYA_RADIX32_ROUNDS - 1) {
            for (size_t doubling = 0; doubling < NARYA_RADIX32_BITS; doubling++)
                narya_edwards_double_x8(&accumulator, &accumulator);
        }
        if ((digits.round[round].nonzero_mask & valid) != 0) {
            narya_projective_niels_x8 selected;
            narya_projective_niels_table_select_x8(
                &selected, table, &digits.round[round], valid);
            narya_edwards_add_projective_niels_x8(
                &accumulator, &accumulator, &selected);
        }
    }
    *out = accumulator;
    return valid;
}
