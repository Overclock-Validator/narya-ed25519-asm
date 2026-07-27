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
