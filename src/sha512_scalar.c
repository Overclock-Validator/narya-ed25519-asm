/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Scalar SHA-512 for the coordinate-packed one- and two-signature path.
 *
 * The x8 compressor is the right shape once several independent messages are
 * present, but transposing one message into eight-lane form is substantial
 * fixed work. This file implements the FIPS 180-4 recurrence directly for
 * the small-batch path. It deliberately shares no compression code or round
 * constants with sha512x8.S, so the two implementations remain useful
 * differential oracles for one another.
 */
#include "internal.h"

#include <stdint.h>
#include <string.h>

static const uint64_t scalar_sha512_initial[8] = {
    UINT64_C(0x6a09e667f3bcc908), UINT64_C(0xbb67ae8584caa73b),
    UINT64_C(0x3c6ef372fe94f82b), UINT64_C(0xa54ff53a5f1d36f1),
    UINT64_C(0x510e527fade682d1), UINT64_C(0x9b05688c2b3e6c1f),
    UINT64_C(0x1f83d9abfb41bd6b), UINT64_C(0x5be0cd19137e2179),
};

static const uint64_t scalar_sha512_round[80] = {
    UINT64_C(0x428a2f98d728ae22), UINT64_C(0x7137449123ef65cd),
    UINT64_C(0xb5c0fbcfec4d3b2f), UINT64_C(0xe9b5dba58189dbbc),
    UINT64_C(0x3956c25bf348b538), UINT64_C(0x59f111f1b605d019),
    UINT64_C(0x923f82a4af194f9b), UINT64_C(0xab1c5ed5da6d8118),
    UINT64_C(0xd807aa98a3030242), UINT64_C(0x12835b0145706fbe),
    UINT64_C(0x243185be4ee4b28c), UINT64_C(0x550c7dc3d5ffb4e2),
    UINT64_C(0x72be5d74f27b896f), UINT64_C(0x80deb1fe3b1696b1),
    UINT64_C(0x9bdc06a725c71235), UINT64_C(0xc19bf174cf692694),
    UINT64_C(0xe49b69c19ef14ad2), UINT64_C(0xefbe4786384f25e3),
    UINT64_C(0x0fc19dc68b8cd5b5), UINT64_C(0x240ca1cc77ac9c65),
    UINT64_C(0x2de92c6f592b0275), UINT64_C(0x4a7484aa6ea6e483),
    UINT64_C(0x5cb0a9dcbd41fbd4), UINT64_C(0x76f988da831153b5),
    UINT64_C(0x983e5152ee66dfab), UINT64_C(0xa831c66d2db43210),
    UINT64_C(0xb00327c898fb213f), UINT64_C(0xbf597fc7beef0ee4),
    UINT64_C(0xc6e00bf33da88fc2), UINT64_C(0xd5a79147930aa725),
    UINT64_C(0x06ca6351e003826f), UINT64_C(0x142929670a0e6e70),
    UINT64_C(0x27b70a8546d22ffc), UINT64_C(0x2e1b21385c26c926),
    UINT64_C(0x4d2c6dfc5ac42aed), UINT64_C(0x53380d139d95b3df),
    UINT64_C(0x650a73548baf63de), UINT64_C(0x766a0abb3c77b2a8),
    UINT64_C(0x81c2c92e47edaee6), UINT64_C(0x92722c851482353b),
    UINT64_C(0xa2bfe8a14cf10364), UINT64_C(0xa81a664bbc423001),
    UINT64_C(0xc24b8b70d0f89791), UINT64_C(0xc76c51a30654be30),
    UINT64_C(0xd192e819d6ef5218), UINT64_C(0xd69906245565a910),
    UINT64_C(0xf40e35855771202a), UINT64_C(0x106aa07032bbd1b8),
    UINT64_C(0x19a4c116b8d2d0c8), UINT64_C(0x1e376c085141ab53),
    UINT64_C(0x2748774cdf8eeb99), UINT64_C(0x34b0bcb5e19b48a8),
    UINT64_C(0x391c0cb3c5c95a63), UINT64_C(0x4ed8aa4ae3418acb),
    UINT64_C(0x5b9cca4f7763e373), UINT64_C(0x682e6ff3d6b2b8a3),
    UINT64_C(0x748f82ee5defb2fc), UINT64_C(0x78a5636f43172f60),
    UINT64_C(0x84c87814a1f0ab72), UINT64_C(0x8cc702081a6439ec),
    UINT64_C(0x90befffa23631e28), UINT64_C(0xa4506cebde82bde9),
    UINT64_C(0xbef9a3f7b2c67915), UINT64_C(0xc67178f2e372532b),
    UINT64_C(0xca273eceea26619c), UINT64_C(0xd186b8c721c0c207),
    UINT64_C(0xeada7dd6cde0eb1e), UINT64_C(0xf57d4f7fee6ed178),
    UINT64_C(0x06f067aa72176fba), UINT64_C(0x0a637dc5a2c898a6),
    UINT64_C(0x113f9804bef90dae), UINT64_C(0x1b710b35131c471b),
    UINT64_C(0x28db77f523047d84), UINT64_C(0x32caab7b40c72493),
    UINT64_C(0x3c9ebe0a15c9bebc), UINT64_C(0x431d67c49c100d4c),
    UINT64_C(0x4cc5d4becb3e42b6), UINT64_C(0x597f299cfc657e2a),
    UINT64_C(0x5fcb6fab3ad6faec), UINT64_C(0x6c44198c4a475817),
};

static inline uint64_t
rotate_right(uint64_t value, unsigned count)
{
    return (value >> count) | (value << (64 - count));
}

static uint64_t
load_be64(const uint8_t input[8])
{
    uint64_t value;
    memcpy(&value, input, sizeof(value));
    return __builtin_bswap64(value);
}

static void
store_be64(uint8_t output[8], uint64_t value)
{
    value = __builtin_bswap64(value);
    memcpy(output, &value, sizeof(value));
}

static void
scalar_sha512_compress(uint64_t state[8], const uint8_t block[128])
{
    uint64_t schedule[16];
    for (size_t word = 0; word < 16; word++)
        schedule[word] = load_be64(&block[word * 8]);

    uint64_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint64_t e = state[4], f = state[5], g = state[6], h = state[7];
    for (size_t round = 0; round < 80; round++) {
        const size_t index = round & 15U;
        if (round >= 16) {
            const uint64_t x = schedule[(round - 15) & 15U];
            const uint64_t y = schedule[(round - 2) & 15U];
            const uint64_t sigma0 =
                rotate_right(x, 1) ^ rotate_right(x, 8) ^ (x >> 7);
            const uint64_t sigma1 =
                rotate_right(y, 19) ^ rotate_right(y, 61) ^ (y >> 6);
            schedule[index] += sigma0 + schedule[(round - 7) & 15U] + sigma1;
        }
        const uint64_t capital_sigma1 =
            rotate_right(e, 14) ^ rotate_right(e, 18) ^ rotate_right(e, 41);
        const uint64_t choose = (e & f) ^ (~e & g);
        const uint64_t t1 = h + capital_sigma1 + choose +
            scalar_sha512_round[round] + schedule[index];
        const uint64_t capital_sigma0 =
            rotate_right(a, 28) ^ rotate_right(a, 34) ^ rotate_right(a, 39);
        const uint64_t majority = (a & b) ^ (a & c) ^ (b & c);
        const uint64_t t2 = capital_sigma0 + majority;
        h = g;
        g = f;
        f = e;
        e = d + t1;
        d = c;
        c = b;
        b = a;
        a = t1 + t2;
    }
    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;
}

narya_status
narya_sha512_r_a_message_scalar(
    uint8_t digest[64],
    const uint8_t r[32],
    const uint8_t a[32],
    const uint8_t *message,
    size_t length)
{
    if (digest == NULL || r == NULL || a == NULL)
        return NARYA_ERR_INVALID_ARGUMENT;
    if (length > SIZE_MAX - 319)
        return NARYA_ERR_RANGE;
    if (message == NULL && length != 0)
        return NARYA_ERR_INVALID_ARGUMENT;

    const size_t total = 64 + length;
    size_t blocks = total / 128 + 1;
    if (total % 128 >= 112)
        blocks++;
    uint64_t state[8];
    memcpy(state, scalar_sha512_initial, sizeof(state));

    for (size_t block_index = 0; block_index < blocks; block_index++) {
        uint8_t block[128] = {0};
        const size_t block_start = block_index * 128;
        if (block_index == 0) {
            memcpy(&block[0], r, 32);
            memcpy(&block[32], a, 32);
            const size_t take = length < 64 ? length : 64;
            if (take != 0)
                memcpy(&block[64], message, take);
        } else {
            const size_t message_start = block_start - 64;
            if (message_start < length) {
                const size_t remaining = length - message_start;
                const size_t take = remaining < 128 ? remaining : 128;
                memcpy(block, &message[message_start], take);
            }
        }
        if (total >= block_start && total < block_start + 128)
            block[total - block_start] = 0x80;
        if (block_index + 1 == blocks) {
            store_be64(&block[112], (uint64_t)total >> 61);
            store_be64(&block[120], (uint64_t)total << 3);
        }
        scalar_sha512_compress(state, block);
    }
    for (size_t word = 0; word < 8; word++)
        store_be64(&digest[word * 8], state[word]);
    return NARYA_OK;
}
