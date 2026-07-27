/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { groups = 32 };

typedef struct fixture_entry {
    uint8_t scalar[32];
    uint8_t expected[32];
} fixture_entry;

static int
hex_nibble(char value)
{
    if (value >= '0' && value <= '9')
        return value - '0';
    if (value >= 'a' && value <= 'f')
        return value - 'a' + 10;
    return -1;
}

static int
parse_hex(uint8_t output[32], const char *hex)
{
    if (strlen(hex) != 64)
        return 0;
    for (size_t index = 0; index < 32; index++) {
        const int high = hex_nibble(hex[2 * index]);
        const int low = hex_nibble(hex[2 * index + 1]);
        if (high < 0 || low < 0)
            return 0;
        output[index] = (uint8_t)(high << 4 | low);
    }
    return 1;
}

static int
load_fixture(const char *path, fixture_entry fixture[groups][8])
{
    FILE *file = fopen(path, "r");
    if (file == NULL)
        return 0;
    uint8_t seen[groups] = {0};
    char line[256];
    while (fgets(line, sizeof(line), file) != NULL) {
        if (line[0] == '#')
            continue;
        size_t group, lane;
        char scalar_hex[65], expected_hex[65];
        if (sscanf(line, "%zu %zu %64s %64s", &group, &lane, scalar_hex,
                   expected_hex) != 4 || group >= groups || lane >= 8 ||
            !parse_hex(fixture[group][lane].scalar, scalar_hex) ||
            !parse_hex(fixture[group][lane].expected, expected_hex)) {
            fclose(file);
            return 0;
        }
        seen[group] |= (uint8_t)(UINT8_C(1) << lane);
    }
    fclose(file);
    for (size_t group = 0; group < groups; group++)
        if (seen[group] != 0xff)
            return 0;
    return 1;
}

static void
canonical_lane(uint64_t output[5], const narya_r51x8 *input, size_t lane)
{
    const uint64_t mask = (UINT64_C(1) << 51) - 1;
    for (size_t limb = 0; limb < 5; limb++)
        output[limb] = input->limb[limb][lane];
    for (size_t round = 0; round < 4; round++) {
        for (size_t limb = 0; limb < 4; limb++) {
            const uint64_t carry = output[limb] >> 51;
            output[limb] &= mask;
            output[limb + 1] += carry;
        }
        const uint64_t carry = output[4] >> 51;
        output[4] &= mask;
        output[0] += 19 * carry;
    }
    if (output[1] == mask && output[2] == mask && output[3] == mask &&
        output[4] == mask && output[0] >= mask - 18) {
        output[0] -= mask - 18;
        output[1] = output[2] = output[3] = output[4] = 0;
    }
}

static int
field_equal_lane(const narya_r51x8 *a, const narya_r51x8 *b, size_t lane)
{
    uint64_t left[5], right[5];
    canonical_lane(left, a, lane);
    canonical_lane(right, b, lane);
    return memcmp(left, right, sizeof(left)) == 0;
}

static int
point_equal(
    const narya_edwards_point_x8 *a,
    const narya_edwards_point_x8 *b)
{
    narya_r51x8 axbz, bxaz, aybz, byaz;
    narya_r51x8_mul_ifma(&axbz, &a->X, &b->Z);
    narya_r51x8_mul_ifma(&bxaz, &b->X, &a->Z);
    narya_r51x8_mul_ifma(&aybz, &a->Y, &b->Z);
    narya_r51x8_mul_ifma(&byaz, &b->Y, &a->Z);
    for (size_t lane = 0; lane < 8; lane++)
        if (!field_equal_lane(&axbz, &bxaz, lane) ||
            !field_equal_lane(&aybz, &byaz, lane))
            return 0;
    return 1;
}

static void
marshal(
    uint8_t scalar[8 * 32],
    uint8_t expected[8 * 32],
    const fixture_entry fixture[8])
{
    for (size_t lane = 0; lane < 8; lane++) {
        memcpy(&scalar[lane * 32], fixture[lane].scalar, 32);
        memcpy(&expected[lane * 32], fixture[lane].expected, 32);
    }
}

int
main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s FIXTURE\n", argv[0]);
        return 1;
    }
    const char *required = getenv("NARYA_REQUIRE_IFMA");
    if (!narya_r51x8_available()) {
        if (required != NULL && required[0] == '1')
            return 1;
        puts("SKIP: AVX-512 IFMA unavailable");
        return 0;
    }

    fixture_entry fixture[groups][8] = {0};
    if (!load_fixture(argv[1], fixture))
        return 1;
    for (size_t group = 0; group < groups; group++) {
        uint8_t scalar[8 * 32], expected_bytes[8 * 32];
        marshal(scalar, expected_bytes, fixture[group]);
        narya_edwards_point_x8 got, expected;
        if (narya_fixed_base_scalar_mult_x8(&got, scalar, 0xff) != 0xff ||
            narya_edwards_decode_x8(&expected, expected_bytes, 0xff) != 0xff ||
            !point_equal(&got, &expected)) {
            fprintf(stderr, "fixed-base comb mismatch group=%zu\n", group);
            return 1;
        }
    }

    uint8_t scalar[8 * 32], expected_bytes[8 * 32];
    marshal(scalar, expected_bytes, fixture[3]);
    for (unsigned int active = 0; active <= 0xff; active++) {
        narya_edwards_point_x8 got, expected;
        if (narya_fixed_base_scalar_mult_x8(
                &got, scalar, (uint8_t)active) != (uint8_t)active ||
            narya_edwards_decode_x8(
                &expected, expected_bytes, (uint8_t)active) != (uint8_t)active ||
            !point_equal(&got, &expected)) {
            fprintf(stderr, "fixed-base active-mask mismatch=%02x\n", active);
            return 1;
        }
    }
    puts("PASS: immutable radix-256 basepoint comb matches affine fixtures");
    return 0;
}
