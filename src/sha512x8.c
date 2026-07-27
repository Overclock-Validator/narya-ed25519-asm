/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

narya_status
narya_sha512_compress_x8(
    narya_sha512_state_x8 *state,
    const narya_sha512_block_x8 *block)
{
    if (state == NULL || block == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;

    /*
     * The complete r51 gate is intentionally stronger than this leaf needs.
     * A standalone verifier binary therefore has one CPU/OS eligibility rule
     * rather than an unsafe call-order-dependent collection of feature gates.
     */
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;
    narya_sha512_compress_x8_asm(state, block);
    return NARYA_OK;
}
