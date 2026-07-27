/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <string.h>

static const narya_projective_niels_micro_entry_x8 identity_entry = {
    .limb = {{1, 1, 1, 0}},
};

static void
store_entry(
    narya_projective_niels_presigned_table_x8 *table,
    size_t entry,
    const narya_projective_niels_x8 *positive)
{
    narya_r51x8 negative_t;
    narya_r51x8_neg_ifma(&negative_t, &positive->T2d);
    for (size_t lane = 0; lane < 8; lane++) {
        for (size_t limb = 0; limb < 5; limb++) {
            table->point[lane][0][entry].limb[limb][0] =
                positive->Y_plus_X.limb[limb][lane];
            table->point[lane][0][entry].limb[limb][1] =
                positive->Y_minus_X.limb[limb][lane];
            table->point[lane][0][entry].limb[limb][2] =
                positive->Z.limb[limb][lane];
            table->point[lane][0][entry].limb[limb][3] =
                positive->T2d.limb[limb][lane];

            /* -(X:Y:Z:T) swaps Y+X/Y-X and negates 2dT. */
            table->point[lane][1][entry].limb[limb][0] =
                positive->Y_minus_X.limb[limb][lane];
            table->point[lane][1][entry].limb[limb][1] =
                positive->Y_plus_X.limb[limb][lane];
            table->point[lane][1][entry].limb[limb][2] =
                positive->Z.limb[limb][lane];
            table->point[lane][1][entry].limb[limb][3] =
                negative_t.limb[limb][lane];
        }
    }
}

void
narya_projective_niels_table_build_x8(
    narya_projective_niels_presigned_table_x8 *out,
    const narya_edwards_point_x8 *base)
{
    narya_edwards_point_x8 current = *base;
    narya_projective_niels_x8 base_cached;
    narya_edwards_to_projective_niels_x8(&base_cached, base);
    store_entry(out, 0, &base_cached);
    for (size_t entry = 1; entry < 16; entry++) {
        narya_edwards_add_projective_niels_x8(
            &current, &current, &base_cached);
        narya_projective_niels_x8 cached;
        narya_edwards_to_projective_niels_x8(&cached, &current);
        store_entry(out, entry, &cached);
    }
}

void
narya_projective_niels_table_select_x8(
    narya_projective_niels_x8 *out,
    const narya_projective_niels_presigned_table_x8 *table,
    const narya_radix32_round_x8 *round,
    uint8_t active)
{
    const uint8_t lookup = round->nonzero_mask & active;
    const uint8_t negative = round->negative_mask & lookup;
    const narya_projective_niels_micro_entry_x8 *source[8];
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = UINT8_C(1) << lane;
        source[lane] = &identity_entry;
        if ((lookup & lane_mask) != 0) {
            const size_t sign = (negative >> lane) & 1u;
            const size_t magnitude = round->magnitude[lane];
            /* The recoder contract makes this index range 0..15 exact. */
            source[lane] = &table->point[lane][sign][magnitude - 1];
        }
    }
    narya_projective_niels_transpose_x8_asm(out, source);
}
