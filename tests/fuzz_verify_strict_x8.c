/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "narya_ed25519_asm.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum {
    lanes = 8,
    public_bytes = lanes * 32,
    signature_bytes = lanes * 64,
    length_bytes = lanes * 2,
    header_bytes = 1 + public_bytes + signature_bytes + length_bytes,
    maximum_message = 4096,
};

static void
fail(void)
{
    abort();
}

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    if (size < header_bytes || !narya_r51x8_available())
        return 0;

    const uint8_t active = data[0];
    const uint8_t *public_key = &data[1];
    const uint8_t *signature = public_key + public_bytes;
    const uint8_t *encoded_length = signature + signature_bytes;
    const uint8_t *cursor = encoded_length + length_bytes;
    size_t remaining = size - header_bytes;
    const uint8_t *message[lanes];
    size_t length[lanes];

    for (size_t lane = 0; lane < lanes; lane++) {
        const size_t requested =
            ((size_t)encoded_length[2 * lane] |
             (size_t)encoded_length[2 * lane + 1] << 8) %
            (maximum_message + 1U);
        length[lane] = requested < remaining ? requested : remaining;
        message[lane] = cursor;
        cursor += length[lane];
        remaining -= length[lane];
    }

    const size_t workspace_size = narya_ed25519_verify_strict_x8_workspace_size();
    void *workspace = malloc(workspace_size);
    if (workspace == NULL)
        return 0;

    uint8_t batch = UINT8_C(0xa5);
    if (narya_ed25519_verify_strict_x8(
            &batch, public_key, signature, message, length, active,
            workspace, workspace_size) != NARYA_OK ||
        (batch & (uint8_t)~active) != 0) {
        free(workspace);
        fail();
    }

    /* A repeated call and every active lane in isolation must agree exactly. */
    uint8_t repeated = UINT8_C(0x5a);
    if (narya_ed25519_verify_strict_x8(
            &repeated, public_key, signature, message, length, active,
            workspace, workspace_size) != NARYA_OK ||
        repeated != batch) {
        free(workspace);
        fail();
    }
    for (size_t lane = 0; lane < lanes; lane++) {
        const uint8_t bit = (uint8_t)(UINT8_C(1) << lane);
        if ((active & bit) == 0)
            continue;
        uint8_t isolated = UINT8_C(0xa5);
        if (narya_ed25519_verify_strict_x8(
                &isolated, public_key, signature, message, length, bit,
                workspace, workspace_size) != NARYA_OK ||
            (isolated & bit) != (batch & bit) || (isolated & (uint8_t)~bit) != 0) {
            free(workspace);
            fail();
        }
    }

    free(workspace);
    return 0;
}
