/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <string.h>

static const uint8_t scalar_order[32] = {
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
};

static int
canonical_scalar(const uint8_t scalar[32])
{
    for (size_t index = 32; index-- > 0;) {
        if (scalar[index] != scalar_order[index])
            return scalar[index] < scalar_order[index];
    }
    return 0;
}

static uint16_t
scalar_bits(const uint8_t scalar[32], size_t bit)
{
    const size_t byte = bit >> 3;
    const unsigned int shift = (unsigned int)(bit & 7);
    uint16_t word = scalar[byte];
    if (byte + 1 < 32)
        word |= (uint16_t)scalar[byte + 1] << 8;
    return (word >> shift) & UINT16_C(31);
}

uint8_t
narya_scalar_recode_radix32_x8(
    narya_radix32_digits_x8 *out,
    const uint8_t scalar[8 * 32],
    uint8_t negative_mask,
    uint8_t active)
{
    if (out == NULL || scalar == NULL)
        return 0;
    memset(out, 0, sizeof(*out));

    uint8_t valid = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = UINT8_C(1) << lane;
        if ((active & lane_mask) != 0 && canonical_scalar(&scalar[lane * 32]))
            valid |= lane_mask;
    }

    /*
     * These are ordinary C integers deliberately.  The recurrence proves
     * carry is 0 or 1 and digit is in [-16, 15], so a narrow integer type
     * adds no safety and forces implementation-noise narrowing conversions.
     */
    int carry[8] = {0};
    for (size_t round = 0; round < NARYA_RADIX32_ROUNDS; round++) {
        narya_radix32_round_x8 *record = &out->round[round];
        const size_t bit = round * NARYA_RADIX32_BITS;
        for (size_t lane = 0; lane < 8; lane++) {
            const uint8_t lane_mask = UINT8_C(1) << lane;
            if ((valid & lane_mask) == 0)
                continue;
            int digit =
                (int)scalar_bits(&scalar[lane * 32], bit) + carry[lane];
            carry[lane] = (digit + 16) / 32;
            digit -= carry[lane] * 32;
            if ((negative_mask & lane_mask) != 0)
                digit = -digit;
            if (digit != 0) {
                record->nonzero_mask |= lane_mask;
                if (digit < 0) {
                    record->negative_mask |= lane_mask;
                    digit = -digit;
                }
                record->magnitude[lane] = (uint8_t)digit;
            }
        }
    }

    /* Canonical scalars are below 2^253, so 51 radix-32 rounds are exact. */
    for (size_t lane = 0; lane < 8; lane++) {
        if (carry[lane] != 0)
            return 0;
    }
    out->valid_mask = valid;
    return valid;
}
