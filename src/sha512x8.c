/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <limits.h>
#include <string.h>

static const uint64_t sha512_initial_state[8] = {
    UINT64_C(0x6a09e667f3bcc908), UINT64_C(0xbb67ae8584caa73b),
    UINT64_C(0x3c6ef372fe94f82b), UINT64_C(0xa54ff53a5f1d36f1),
    UINT64_C(0x510e527fade682d1), UINT64_C(0x9b05688c2b3e6c1f),
    UINT64_C(0x1f83d9abfb41bd6b), UINT64_C(0x5be0cd19137e2179),
};

static uint64_t
load64_be(const uint8_t input[8])
{
    uint64_t value = 0;
    for (size_t i = 0; i < 8; i++)
        value = (value << 8) | input[i];
    return value;
}

static void
store64_be(uint8_t output[8], uint64_t value)
{
    for (size_t i = 0; i < 8; i++) {
        output[7 - i] = (uint8_t)value;
        value >>= 8;
    }
}

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

narya_status
narya_sha512_r_a_message_x8(
    uint8_t digest[NARYA_X8_LANES][64],
    const uint8_t r[NARYA_X8_LANES * 32],
    const uint8_t a[NARYA_X8_LANES * 32],
    const uint8_t *const message[NARYA_X8_LANES],
    const size_t length[NARYA_X8_LANES],
    uint8_t active)
{
    if (digest == NULL || r == NULL || a == NULL ||
        message == NULL || length == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;

    size_t blocks[8] = {0};
    size_t max_blocks = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) == 0)
            continue;
        /* Keep padded block addressing representable in size_t as well. */
        if (length[lane] > SIZE_MAX - 319)
            return NARYA_ERR_RANGE;
        if (message[lane] == NULL && length[lane] != 0)
            return NARYA_ERR_INVALID_ARGUMENT;
        const size_t total = 64 + length[lane];
        blocks[lane] = total / 128 + 1;
        if (total % 128 >= 112)
            blocks[lane]++;
        if (blocks[lane] > max_blocks)
            max_blocks = blocks[lane];
    }

    uint8_t result[8][64] = {{0}};
    narya_sha512_state_x8 state;
    for (size_t word = 0; word < 8; word++)
        for (size_t lane = 0; lane < 8; lane++)
            state.word[word][lane] = sha512_initial_state[word];

    for (size_t block_index = 0; block_index < max_blocks; block_index++) {
        uint8_t raw[8][128] = {{0}};
        narya_sha512_block_x8 block;
        for (size_t lane = 0; lane < 8; lane++) {
            if (block_index >= blocks[lane])
                continue;
            const size_t total = 64 + length[lane];
            const size_t block_start = block_index * 128;
            for (size_t offset = 0; offset < 128; offset++) {
                const size_t position = block_start + offset;
                if (position < 32)
                    raw[lane][offset] = r[lane * 32 + position];
                else if (position < 64)
                    raw[lane][offset] = a[lane * 32 + position - 32];
                else if (position < total)
                    raw[lane][offset] = message[lane][position - 64];
            }
            if (total >= block_start && total < block_start + 128)
                raw[lane][total - block_start] = 0x80;
            if (block_index + 1 == blocks[lane]) {
                store64_be(&raw[lane][112], (uint64_t)total >> 61);
                store64_be(&raw[lane][120], (uint64_t)total << 3);
            }
        }
        for (size_t word = 0; word < 16; word++)
            for (size_t lane = 0; lane < 8; lane++)
                block.word[word][lane] = load64_be(&raw[lane][word * 8]);

        narya_sha512_compress_x8_asm(&state, &block);
        for (size_t lane = 0; lane < 8; lane++) {
            if (block_index + 1 != blocks[lane])
                continue;
            for (size_t word = 0; word < 8; word++)
                store64_be(&result[lane][word * 8], state.word[word][lane]);
        }
    }
    memcpy(digest, result, sizeof(result));
    return NARYA_OK;
}
