/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Independent scalar oracle and FIPS-known-answer gate for the SysV x8
 * SHA-512 compression leaf. This file intentionally does not share the
 * assembly macro schedule or its rolling sixteen-register recurrence.
 */
#include "narya_ed25519_asm.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint64_t round_constants[80] = {
    UINT64_C(0x428a2f98d728ae22),
    UINT64_C(0x7137449123ef65cd),
    UINT64_C(0xb5c0fbcfec4d3b2f),
    UINT64_C(0xe9b5dba58189dbbc),
    UINT64_C(0x3956c25bf348b538),
    UINT64_C(0x59f111f1b605d019),
    UINT64_C(0x923f82a4af194f9b),
    UINT64_C(0xab1c5ed5da6d8118),
    UINT64_C(0xd807aa98a3030242),
    UINT64_C(0x12835b0145706fbe),
    UINT64_C(0x243185be4ee4b28c),
    UINT64_C(0x550c7dc3d5ffb4e2),
    UINT64_C(0x72be5d74f27b896f),
    UINT64_C(0x80deb1fe3b1696b1),
    UINT64_C(0x9bdc06a725c71235),
    UINT64_C(0xc19bf174cf692694),
    UINT64_C(0xe49b69c19ef14ad2),
    UINT64_C(0xefbe4786384f25e3),
    UINT64_C(0x0fc19dc68b8cd5b5),
    UINT64_C(0x240ca1cc77ac9c65),
    UINT64_C(0x2de92c6f592b0275),
    UINT64_C(0x4a7484aa6ea6e483),
    UINT64_C(0x5cb0a9dcbd41fbd4),
    UINT64_C(0x76f988da831153b5),
    UINT64_C(0x983e5152ee66dfab),
    UINT64_C(0xa831c66d2db43210),
    UINT64_C(0xb00327c898fb213f),
    UINT64_C(0xbf597fc7beef0ee4),
    UINT64_C(0xc6e00bf33da88fc2),
    UINT64_C(0xd5a79147930aa725),
    UINT64_C(0x06ca6351e003826f),
    UINT64_C(0x142929670a0e6e70),
    UINT64_C(0x27b70a8546d22ffc),
    UINT64_C(0x2e1b21385c26c926),
    UINT64_C(0x4d2c6dfc5ac42aed),
    UINT64_C(0x53380d139d95b3df),
    UINT64_C(0x650a73548baf63de),
    UINT64_C(0x766a0abb3c77b2a8),
    UINT64_C(0x81c2c92e47edaee6),
    UINT64_C(0x92722c851482353b),
    UINT64_C(0xa2bfe8a14cf10364),
    UINT64_C(0xa81a664bbc423001),
    UINT64_C(0xc24b8b70d0f89791),
    UINT64_C(0xc76c51a30654be30),
    UINT64_C(0xd192e819d6ef5218),
    UINT64_C(0xd69906245565a910),
    UINT64_C(0xf40e35855771202a),
    UINT64_C(0x106aa07032bbd1b8),
    UINT64_C(0x19a4c116b8d2d0c8),
    UINT64_C(0x1e376c085141ab53),
    UINT64_C(0x2748774cdf8eeb99),
    UINT64_C(0x34b0bcb5e19b48a8),
    UINT64_C(0x391c0cb3c5c95a63),
    UINT64_C(0x4ed8aa4ae3418acb),
    UINT64_C(0x5b9cca4f7763e373),
    UINT64_C(0x682e6ff3d6b2b8a3),
    UINT64_C(0x748f82ee5defb2fc),
    UINT64_C(0x78a5636f43172f60),
    UINT64_C(0x84c87814a1f0ab72),
    UINT64_C(0x8cc702081a6439ec),
    UINT64_C(0x90befffa23631e28),
    UINT64_C(0xa4506cebde82bde9),
    UINT64_C(0xbef9a3f7b2c67915),
    UINT64_C(0xc67178f2e372532b),
    UINT64_C(0xca273eceea26619c),
    UINT64_C(0xd186b8c721c0c207),
    UINT64_C(0xeada7dd6cde0eb1e),
    UINT64_C(0xf57d4f7fee6ed178),
    UINT64_C(0x06f067aa72176fba),
    UINT64_C(0x0a637dc5a2c898a6),
    UINT64_C(0x113f9804bef90dae),
    UINT64_C(0x1b710b35131c471b),
    UINT64_C(0x28db77f523047d84),
    UINT64_C(0x32caab7b40c72493),
    UINT64_C(0x3c9ebe0a15c9bebc),
    UINT64_C(0x431d67c49c100d4c),
    UINT64_C(0x4cc5d4becb3e42b6),
    UINT64_C(0x597f299cfc657e2a),
    UINT64_C(0x5fcb6fab3ad6faec),
    UINT64_C(0x6c44198c4a475817)
};

static const uint64_t initial_state[8] = {
    UINT64_C(0x6a09e667f3bcc908), UINT64_C(0xbb67ae8584caa73b),
    UINT64_C(0x3c6ef372fe94f82b), UINT64_C(0xa54ff53a5f1d36f1),
    UINT64_C(0x510e527fade682d1), UINT64_C(0x9b05688c2b3e6c1f),
    UINT64_C(0x1f83d9abfb41bd6b), UINT64_C(0x5be0cd19137e2179),
};

static uint64_t random_state = UINT64_C(0x9e3779b97f4a7c15);

static uint64_t
random64(void)
{
    uint64_t x = random_state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    random_state = x;
    return x * UINT64_C(0x2545f4914f6cdd1d);
}

static uint64_t
rotate_right(uint64_t x, unsigned int count)
{
    return (x >> count) | (x << (64 - count));
}

static void
reference_compress(uint64_t state[8], const uint64_t block[16])
{
    uint64_t schedule[80];
    memcpy(schedule, block, 16 * sizeof(uint64_t));
    for (size_t i = 16; i < 80; i++) {
        const uint64_t x = schedule[i - 15];
        const uint64_t y = schedule[i - 2];
        const uint64_t sigma0 =
            rotate_right(x, 1) ^ rotate_right(x, 8) ^ (x >> 7);
        const uint64_t sigma1 =
            rotate_right(y, 19) ^ rotate_right(y, 61) ^ (y >> 6);
        schedule[i] = schedule[i - 16] + sigma0 +
                      schedule[i - 7] + sigma1;
    }

    uint64_t a = state[0];
    uint64_t b = state[1];
    uint64_t c = state[2];
    uint64_t d = state[3];
    uint64_t e = state[4];
    uint64_t f = state[5];
    uint64_t g = state[6];
    uint64_t h = state[7];
    for (size_t i = 0; i < 80; i++) {
        const uint64_t capital_sigma1 =
            rotate_right(e, 14) ^ rotate_right(e, 18) ^ rotate_right(e, 41);
        const uint64_t choose = (e & f) ^ (~e & g);
        const uint64_t t1 =
            h + capital_sigma1 + choose + round_constants[i] + schedule[i];
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

static int
check_empty_digest(void)
{
    static const uint64_t empty_digest[8] = {
        UINT64_C(0xcf83e1357eefb8bd), UINT64_C(0xf1542850d66d8007),
        UINT64_C(0xd620e4050b5715dc), UINT64_C(0x83f4a921d36ce9ce),
        UINT64_C(0x47d0d13c5d85f2b0), UINT64_C(0xff8318d2877eec2f),
        UINT64_C(0x63b931bd47417a81), UINT64_C(0xa538327af927da3e),
    };
    narya_sha512_state_x8 state;
    narya_sha512_block_x8 block = {0};
    for (size_t word = 0; word < 8; word++)
        for (size_t lane = 0; lane < 8; lane++)
            state.word[word][lane] = initial_state[word];
    for (size_t lane = 0; lane < 8; lane++)
        block.word[0][lane] = UINT64_C(0x8000000000000000);

    if (narya_sha512_compress_x8(&state, &block) != NARYA_OK)
        return 0;
    for (size_t word = 0; word < 8; word++) {
        for (size_t lane = 0; lane < 8; lane++) {
            if (state.word[word][lane] != empty_digest[word]) {
                fprintf(stderr,
                    "empty SHA-512 mismatch word=%zu lane=%zu "
                    "got=%016" PRIx64 " want=%016" PRIx64 "\n",
                    word, lane, state.word[word][lane], empty_digest[word]);
                return 0;
            }
        }
    }
    return 1;
}

static int
check_random_compressions(void)
{
    for (size_t iteration = 0; iteration < 2000; iteration++) {
        narya_sha512_state_x8 state;
        narya_sha512_state_x8 expected;
        narya_sha512_block_x8 block;
        for (size_t word = 0; word < 8; word++) {
            for (size_t lane = 0; lane < 8; lane++) {
                state.word[word][lane] = random64();
                expected.word[word][lane] = state.word[word][lane];
            }
        }
        for (size_t word = 0; word < 16; word++)
            for (size_t lane = 0; lane < 8; lane++)
                block.word[word][lane] = random64();

        for (size_t lane = 0; lane < 8; lane++) {
            uint64_t lane_state[8];
            uint64_t lane_block[16];
            for (size_t word = 0; word < 8; word++)
                lane_state[word] = expected.word[word][lane];
            for (size_t word = 0; word < 16; word++)
                lane_block[word] = block.word[word][lane];
            reference_compress(lane_state, lane_block);
            for (size_t word = 0; word < 8; word++)
                expected.word[word][lane] = lane_state[word];
        }

        if (narya_sha512_compress_x8(&state, &block) != NARYA_OK)
            return 0;
        if (memcmp(&state, &expected, sizeof(state)) != 0) {
            fprintf(stderr, "random SHA-512 compression mismatch at %zu\n", iteration);
            return 0;
        }
    }
    return 1;
}

int
main(void)
{
    if (!narya_r51x8_available()) {
        if (getenv("NARYA_REQUIRE_IFMA") != NULL) {
            fputs("FAIL: native AVX-512 execution was required but unavailable\n", stderr);
            return 1;
        }
        puts("SKIP: full Narya AVX-512 feature set is unavailable");
        return 0;
    }
    if (narya_sha512_compress_x8(NULL, NULL) != NARYA_ERR_INVALID_ARGUMENT) {
        fputs("SHA-512 null argument was not rejected\n", stderr);
        return 1;
    }
    if (!check_empty_digest() || !check_random_compressions())
        return 1;
    puts("PASS: x8 SHA-512 compression matches scalar and known-answer oracles");
    return 0;
}
