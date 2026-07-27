/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t scalar_order[32] = {
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
};

static uint64_t random_state = UINT64_C(0x693f4b28d175ace1);

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

static int
canonical(const uint8_t scalar[32])
{
    for (size_t index = 32; index-- > 0;) {
        if (scalar[index] != scalar_order[index])
            return scalar[index] < scalar_order[index];
    }
    return 0;
}

static void
subtract_order(uint8_t scalar[32])
{
    unsigned int borrow = 0;
    for (size_t index = 0; index < 32; index++) {
        const unsigned int subtrahend = scalar_order[index] + borrow;
        const unsigned int value = scalar[index];
        scalar[index] = (uint8_t)(value - subtrahend);
        borrow = value < subtrahend;
    }
}

static void
make_canonical(uint8_t scalar[32])
{
    /* Any 256-bit integer is below 16*l; repeated subtraction is bounded. */
    while (!canonical(scalar))
        subtract_order(scalar);
}

/*
 * Reconstruct the signed digits modulo 2^320. Because both the requested
 * integer and digit expansion have magnitude below 2^253, equality in this
 * wider ring is equality as signed integers, not merely modulo l.
 */
static void
reconstruct(uint64_t out[5], const narya_radix32_digits_x8 *digits, size_t lane)
{
    memset(out, 0, 5 * sizeof(uint64_t));
    for (size_t round = NARYA_RADIX32_ROUNDS; round-- > 0;) {
        uint64_t carry = 0;
        for (size_t word = 0; word < 5; word++) {
            const uint64_t next = out[word] >> 59;
            out[word] = (out[word] << 5) | carry;
            carry = next;
        }
        const narya_radix32_round_x8 *record = &digits->round[round];
        const uint8_t lane_mask = UINT8_C(1) << lane;
        uint64_t magnitude = record->magnitude[lane];
        if ((record->negative_mask & lane_mask) == 0) {
            for (size_t word = 0; word < 5 && magnitude != 0; word++) {
                const uint64_t before = out[word];
                out[word] += magnitude;
                magnitude = out[word] < before;
            }
        } else {
            uint64_t borrow = magnitude;
            for (size_t word = 0; word < 5 && borrow != 0; word++) {
                const uint64_t before = out[word];
                out[word] -= borrow;
                borrow = before < borrow;
            }
        }
    }
}

static uint64_t
load64_le(const uint8_t input[8])
{
    uint64_t value = 0;
    for (size_t i = 0; i < 8; i++)
        value |= (uint64_t)input[i] << (8 * i);
    return value;
}

static void
expected_integer(uint64_t out[5], const uint8_t scalar[32], int negative)
{
    for (size_t word = 0; word < 4; word++)
        out[word] = load64_le(&scalar[word * 8]);
    out[4] = 0;
    if (!negative)
        return;
    uint64_t carry = 1;
    for (size_t word = 0; word < 5; word++) {
        out[word] = ~out[word];
        const uint64_t before = out[word];
        out[word] += carry;
        carry = carry != 0 && out[word] < before;
    }
}

static int
check_digits(uint8_t scalars[8][32], uint8_t active, uint8_t signs)
{
    narya_radix32_digits_x8 digits;
    const uint8_t valid = narya_scalar_recode_radix32_x8(
        &digits, &scalars[0][0], signs, active);
    uint8_t want_valid = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = UINT8_C(1) << lane;
        if ((active & lane_mask) != 0 && canonical(scalars[lane]))
            want_valid |= lane_mask;
    }
    if (valid != want_valid || digits.valid_mask != want_valid)
        return 0;

    for (size_t round = 0; round < NARYA_RADIX32_ROUNDS; round++) {
        const narya_radix32_round_x8 *record = &digits.round[round];
        for (size_t lane = 0; lane < 8; lane++) {
            const uint8_t lane_mask = UINT8_C(1) << lane;
            const uint8_t magnitude = record->magnitude[lane];
            if (magnitude > 16)
                return 0;
            if ((want_valid & lane_mask) == 0 &&
                (magnitude != 0 || (record->nonzero_mask & lane_mask) != 0 ||
                 (record->negative_mask & lane_mask) != 0))
                return 0;
            if (((record->nonzero_mask & lane_mask) != 0) != (magnitude != 0))
                return 0;
            if (magnitude == 0 && (record->negative_mask & lane_mask) != 0)
                return 0;
        }
    }
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = UINT8_C(1) << lane;
        if ((want_valid & lane_mask) == 0)
            continue;
        uint64_t got[5];
        uint64_t want[5];
        reconstruct(got, &digits, lane);
        expected_integer(want, scalars[lane], (signs & lane_mask) != 0);
        if (memcmp(got, want, sizeof(got)) != 0) {
            fprintf(stderr, "exact recoding mismatch lane=%zu\n", lane);
            return 0;
        }
    }
    return 1;
}

int
main(void)
{
    uint8_t scalars[8][32] = {{0}};
    scalars[1][0] = 1;
    memcpy(scalars[2], scalar_order, 32);
    memcpy(scalars[3], scalar_order, 32);
    scalars[3][0]--;
    memset(scalars[4], 0xff, 32);
    for (size_t lane = 5; lane < 8; lane++) {
        for (size_t i = 0; i < 32; i++)
            scalars[lane][i] = (uint8_t)random64();
        make_canonical(scalars[lane]);
    }
    for (unsigned int active = 0; active <= 0xff; active++) {
        if (!check_digits(scalars, (uint8_t)active, (uint8_t)(active ^ 0xa5))) {
            fprintf(stderr, "edge/mask recoding mismatch active=%02x\n", active);
            return 1;
        }
    }
    for (size_t iteration = 0; iteration < 10000; iteration++) {
        for (size_t lane = 0; lane < 8; lane++) {
            for (size_t i = 0; i < 32; i++)
                scalars[lane][i] = (uint8_t)random64();
            make_canonical(scalars[lane]);
        }
        if (!check_digits(scalars, 0xff, (uint8_t)random64()))
            return 1;
    }
    puts("PASS: round-major radix-32 recoding is an exact signed integer map");
    return 0;
}
