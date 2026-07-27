/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Structurally independent oracle for the x8 signed-radix-2^21 reducer.
 * The oracle performs 512 shift/conditional-subtract steps directly against
 * the literal group order. It shares neither limbs, fold constants, carries,
 * nor packing expressions with scalar_reduce_x8.S.
 */
#include "narya_ed25519_asm.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t scalar_order_bytes[32] = {
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
};

static const uint64_t scalar_order_words[4] = {
    UINT64_C(0x5812631a5cf5d3ed), UINT64_C(0x14def9dea2f79cd6),
    UINT64_C(0x0000000000000000), UINT64_C(0x1000000000000000),
};

static uint64_t random_state = UINT64_C(0x8f4d2a71e6c39b05);

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

static void
store64_le(uint8_t output[8], uint64_t value)
{
    for (size_t i = 0; i < 8; i++) {
        output[i] = (uint8_t)value;
        value >>= 8;
    }
}

static int
words_greater_or_equal(const uint64_t x[4], const uint64_t y[4])
{
    for (size_t i = 4; i-- > 0;) {
        if (x[i] != y[i])
            return x[i] > y[i];
    }
    return 1;
}

static void
subtract_words(uint64_t x[4], const uint64_t y[4])
{
    uint64_t borrow = 0;
    for (size_t i = 0; i < 4; i++) {
        const uint64_t yi = y[i] + borrow;
        const uint64_t carry = yi < y[i];
        const uint64_t next = x[i] - yi;
        borrow = carry | (x[i] < yi);
        x[i] = next;
    }
}

static void
reference_reduce(uint8_t output[32], const uint8_t input[64])
{
    uint64_t residue[4] = {0};
    for (size_t bit = 512; bit-- > 0;) {
        uint64_t carry = (input[bit / 8] >> (bit % 8)) & 1u;
        for (size_t word = 0; word < 4; word++) {
            const uint64_t next = residue[word] >> 63;
            residue[word] = (residue[word] << 1) | carry;
            carry = next;
        }
        if (words_greater_or_equal(residue, scalar_order_words))
            subtract_words(residue, scalar_order_words);
    }
    for (size_t word = 0; word < 4; word++)
        store64_le(&output[word * 8], residue[word]);
}

static void
add_one(uint8_t value[64])
{
    for (size_t i = 0; i < 64; i++) {
        value[i]++;
        if (value[i] != 0)
            break;
    }
}

static void
subtract_one(uint8_t value[64])
{
    for (size_t i = 0; i < 64; i++) {
        const uint8_t before = value[i];
        value[i]--;
        if (before != 0)
            break;
    }
}

static void
double_order(uint8_t value[64])
{
    unsigned int carry = 0;
    for (size_t i = 0; i < 32; i++) {
        const unsigned int doubled =
            (unsigned int)scalar_order_bytes[i] * 2U + carry;
        value[i] = (uint8_t)doubled;
        carry = doubled >> 8;
    }
    value[32] = (uint8_t)carry;
}

static int
canonical(const uint8_t scalar[32])
{
    for (size_t i = 32; i-- > 0;) {
        if (scalar[i] != scalar_order_bytes[i])
            return scalar[i] < scalar_order_bytes[i];
    }
    return 0;
}

static int
check_case(uint8_t input[8][64], uint8_t active, const char *label)
{
    uint8_t got[8][32];
    uint8_t want[8][32] = {{0}};
    memset(got, 0xa5, sizeof(got));
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) != 0)
            reference_reduce(want[lane], input[lane]);
    }
    if (narya_scalar_reduce_x8(got, &input[0][0], active) != NARYA_OK) {
        fprintf(stderr, "%s: reducer returned an error\n", label);
        return 0;
    }
    if (memcmp(got, want, sizeof(got)) != 0) {
        for (size_t lane = 0; lane < 8; lane++) {
            if (memcmp(got[lane], want[lane], 32) != 0) {
                fprintf(stderr, "%s: mismatch in lane %zu active=%02x\n",
                        label, lane, active);
                break;
            }
        }
        return 0;
    }
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) != 0 && !canonical(got[lane])) {
            fprintf(stderr, "%s: noncanonical lane %zu\n", label, lane);
            return 0;
        }
    }
    return 1;
}

static int
check_edges_and_masks(void)
{
    uint8_t input[8][64] = {{0}};
    input[1][0] = 1;
    memcpy(input[2], scalar_order_bytes, 32);
    memcpy(input[3], scalar_order_bytes, 32);
    subtract_one(input[3]);
    memcpy(input[4], scalar_order_bytes, 32);
    add_one(input[4]);
    memset(input[5], 0xff, 64);
    input[6][63] = 0x80;
    double_order(input[7]);
    if (!check_case(input, 0xff, "edge vectors"))
        return 0;

    for (size_t lane = 0; lane < 8; lane++)
        for (size_t i = 0; i < 64; i++)
            input[lane][i] = (uint8_t)random64();
    for (unsigned int mask = 0; mask <= 0xff; mask++) {
        if (!check_case(input, (uint8_t)mask, "active-mask sweep"))
            return 0;
    }
    return 1;
}

static int
check_random_and_alias(void)
{
    uint8_t input[8][64];
    for (size_t iteration = 0; iteration < 10000; iteration++) {
        for (size_t lane = 0; lane < 8; lane++)
            for (size_t i = 0; i < 64; i++)
                input[lane][i] = (uint8_t)random64();
        if (!check_case(input, 0xff, "random differential"))
            return 0;
    }

    union {
        uint64_t align;
        uint8_t bytes[8 * 64];
    } storage;
    for (size_t i = 0; i < sizeof(storage.bytes); i++)
        storage.bytes[i] = (uint8_t)random64();
    uint8_t original[8][64];
    memcpy(original, storage.bytes, sizeof(original));
    uint8_t want[8][32];
    for (size_t lane = 0; lane < 8; lane++)
        reference_reduce(want[lane], original[lane]);
    if (narya_scalar_reduce_x8(
            (uint8_t (*)[32])storage.bytes, storage.bytes, 0xff) != NARYA_OK ||
        memcmp(storage.bytes, want, sizeof(want)) != 0) {
        fputs("exact source/output alias mismatch\n", stderr);
        return 0;
    }
    return 1;
}

static int
check_error_atomicity(void)
{
    uint8_t output[8][32];
    uint8_t unchanged[8][32];
    memset(output, 0xa5, sizeof(output));
    memcpy(unchanged, output, sizeof(output));
    if (narya_scalar_reduce_x8(output, NULL, 0xff) !=
            NARYA_ERR_INVALID_ARGUMENT ||
        memcmp(output, unchanged, sizeof(output)) != 0)
        return 0;
    return 1;
}

int
main(void)
{
    const char *required = getenv("NARYA_REQUIRE_IFMA");
    if (!narya_r51x8_available()) {
        if (required != NULL && required[0] == '1') {
            fputs("AVX-512 IFMA required but unavailable\n", stderr);
            return 1;
        }
        puts("SKIP: AVX-512 IFMA unavailable");
        return 0;
    }
    if (!check_edges_and_masks() || !check_random_and_alias() ||
        !check_error_atomicity())
        return 1;
    puts("PASS: x8 scalar reduction matches independent modulo-l oracle");
    return 0;
}
