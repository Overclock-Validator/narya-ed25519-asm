/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <string.h>

static int
narya_r51x8_is_u52(const narya_r51x8 *x)
{
    const uint64_t limit = UINT64_C(1) << 52;
    uint64_t bad = 0;

    for (size_t limb = 0; limb < NARYA_R51_LIMBS; limb++)
        for (size_t lane = 0; lane < NARYA_X8_LANES; lane++)
            bad |= x->limb[limb][lane] >= limit;
    return bad == 0;
}

void
narya_r51x8_canonical_lane(
    uint64_t output[5],
    const narya_r51x8 *input,
    size_t lane)
{
    const uint64_t mask51 = (UINT64_C(1) << 51) - 1;
    for (size_t limb = 0; limb < 5; limb++)
        output[limb] = input->limb[limb][lane];

    /* Four sequential passes are sufficient from the composable u52 domain. */
    for (size_t round = 0; round < 4; round++) {
        for (size_t limb = 0; limb < 4; limb++) {
            const uint64_t carry = output[limb] >> 51;
            output[limb] &= mask51;
            output[limb + 1] += carry;
        }
        const uint64_t carry = output[4] >> 51;
        output[4] &= mask51;
        output[0] += 19 * carry;
    }

    /* Now 0 <= value < 2^255=p+19; only p..p+18 need subtraction. */
    if (output[1] == mask51 && output[2] == mask51 &&
        output[3] == mask51 && output[4] == mask51 &&
        output[0] >= mask51 - 18) {
        output[0] -= mask51 - 18;
        output[1] = output[2] = output[3] = output[4] = 0;
    }
}

narya_status
narya_r51x8_mul(narya_r51x8 *out, const narya_r51x8 *x, const narya_r51x8 *y)
{
    if (out == NULL || x == NULL || y == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;
    if (!narya_r51x8_is_u52(x) || !narya_r51x8_is_u52(y))
        return NARYA_ERR_RANGE;

    /* The assembly loads all ten source vectors before its first store. */
    narya_r51x8_mul_ifma(out, x, y);
    return NARYA_OK;
}

static narya_status
narya_r51x8_check_binary(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y)
{
    if (out == NULL || x == NULL || y == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;
    if (!narya_r51x8_is_u52(x) || !narya_r51x8_is_u52(y))
        return NARYA_ERR_RANGE;
    return NARYA_OK;
}

narya_status
narya_r51x8_add(narya_r51x8 *out, const narya_r51x8 *x, const narya_r51x8 *y)
{
    const narya_status status = narya_r51x8_check_binary(out, x, y);
    if (status != NARYA_OK)
        return status;
    narya_r51x8_add_ifma(out, x, y);
    return NARYA_OK;
}

narya_status
narya_r51x8_sub(narya_r51x8 *out, const narya_r51x8 *x, const narya_r51x8 *y)
{
    const narya_status status = narya_r51x8_check_binary(out, x, y);
    if (status != NARYA_OK)
        return status;
    narya_r51x8_sub_ifma(out, x, y);
    return NARYA_OK;
}

narya_status
narya_r51x8_neg(narya_r51x8 *out, const narya_r51x8 *x)
{
    if (out == NULL || x == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;
    if (!narya_r51x8_is_u52(x))
        return NARYA_ERR_RANGE;
    narya_r51x8_neg_ifma(out, x);
    return NARYA_OK;
}
