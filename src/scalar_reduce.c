/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <string.h>

/* Load four little-endian bytes without imposing alignment requirements. */
static int64_t
load4_le(const uint8_t input[4])
{
    return (int64_t)input[0] |
           (int64_t)input[1] << 8 |
           (int64_t)input[2] << 16 |
           (int64_t)input[3] << 24;
}

/*
 * The native reducer works in structure-of-arrays radix 2^21. Keeping this
 * byte-to-limb boundary in C makes the signed schedule in
 * scalar_reduce_x8.S directly comparable with the ref10 algebra while the
 * public ABI remains lane-major bytes. Limbs 0..22 are 21 bits; limb 23 is
 * the remaining 29 bits of the 512-bit digest.
 */
static void
load_radix21_x8(
    int64_t limbs[24][8],
    const uint8_t input[8 * 64],
    uint8_t active)
{
    memset(limbs, 0, 24 * 8 * sizeof(int64_t));
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) == 0)
            continue;
        const uint8_t *source = &input[lane * 64];
        for (size_t index = 0; index < 23; index++) {
            const size_t bit = index * 21;
            limbs[index][lane] =
                (load4_le(&source[bit / 8]) >> (bit % 8)) &
                INT64_C(0x1fffff);
        }
        limbs[23][lane] = load4_le(&source[60]) >> 3;
    }
}

/*
 * Pack the final twelve nonnegative radix-2^21 coefficients. Coefficients
 * 0..10 are below 2^21. Coefficient 11 may equal 2^21: canonical scalars in
 * [2^252,l), including l-1, use bit 252. The reduction schedule, not this
 * byte serializer, establishes that the reconstructed integer is below l.
 */
static void
store_radix21(uint8_t output[32], int64_t s[24][8], size_t lane)
{
    output[0] = (uint8_t)s[0][lane];
    output[1] = (uint8_t)(s[0][lane] >> 8);
    output[2] = (uint8_t)((s[0][lane] >> 16) | (s[1][lane] << 5));
    output[3] = (uint8_t)(s[1][lane] >> 3);
    output[4] = (uint8_t)(s[1][lane] >> 11);
    output[5] = (uint8_t)((s[1][lane] >> 19) | (s[2][lane] << 2));
    output[6] = (uint8_t)(s[2][lane] >> 6);
    output[7] = (uint8_t)((s[2][lane] >> 14) | (s[3][lane] << 7));
    output[8] = (uint8_t)(s[3][lane] >> 1);
    output[9] = (uint8_t)(s[3][lane] >> 9);
    output[10] = (uint8_t)((s[3][lane] >> 17) | (s[4][lane] << 4));
    output[11] = (uint8_t)(s[4][lane] >> 4);
    output[12] = (uint8_t)(s[4][lane] >> 12);
    output[13] = (uint8_t)((s[4][lane] >> 20) | (s[5][lane] << 1));
    output[14] = (uint8_t)(s[5][lane] >> 7);
    output[15] = (uint8_t)((s[5][lane] >> 15) | (s[6][lane] << 6));
    output[16] = (uint8_t)(s[6][lane] >> 2);
    output[17] = (uint8_t)(s[6][lane] >> 10);
    output[18] = (uint8_t)((s[6][lane] >> 18) | (s[7][lane] << 3));
    output[19] = (uint8_t)(s[7][lane] >> 5);
    output[20] = (uint8_t)(s[7][lane] >> 13);
    output[21] = (uint8_t)s[8][lane];
    output[22] = (uint8_t)(s[8][lane] >> 8);
    output[23] = (uint8_t)((s[8][lane] >> 16) | (s[9][lane] << 5));
    output[24] = (uint8_t)(s[9][lane] >> 3);
    output[25] = (uint8_t)(s[9][lane] >> 11);
    output[26] = (uint8_t)((s[9][lane] >> 19) | (s[10][lane] << 2));
    output[27] = (uint8_t)(s[10][lane] >> 6);
    output[28] = (uint8_t)((s[10][lane] >> 14) | (s[11][lane] << 7));
    output[29] = (uint8_t)(s[11][lane] >> 1);
    output[30] = (uint8_t)(s[11][lane] >> 9);
    output[31] = (uint8_t)(s[11][lane] >> 17);
}

narya_status
narya_scalar_reduce_x8(
    uint8_t out[8][32],
    const uint8_t input[8 * 64],
    uint8_t active)
{
    if (out == NULL || input == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;

    /* Parse every source first, preserving arbitrary source/output overlap. */
    int64_t limbs[24][8];
    load_radix21_x8(limbs, input, active);
    narya_scalar_reduce_radix21_x8_asm(limbs);

    uint8_t result[8][32] = {{0}};
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) != 0)
            store_radix21(result[lane], limbs, lane);
    }
    memcpy(out, result, sizeof(result));
    return NARYA_OK;
}
