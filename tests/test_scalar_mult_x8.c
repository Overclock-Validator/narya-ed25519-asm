/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { fixture_groups = 32 };

typedef struct scalar_fixture {
    uint8_t scalar[32];
    uint8_t negative;
    uint8_t expected[32];
} scalar_fixture;

static const uint8_t scalar_order[32] = {
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
};

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
    for (size_t byte = 0; byte < 32; byte++) {
        const int high = hex_nibble(hex[2 * byte]);
        const int low = hex_nibble(hex[2 * byte + 1]);
        if (high < 0 || low < 0)
            return 0;
        output[byte] = (uint8_t)(high << 4 | low);
    }
    return 1;
}

static int
load_basepoints(const char *path, uint8_t encoded[8 * 32])
{
    FILE *file = fopen(path, "r");
    if (file == NULL)
        return 0;
    char line[256];
    uint8_t seen = 0;
    while (fgets(line, sizeof(line), file) != NULL) {
        if (line[0] == '#')
            continue;
        size_t scalar;
        char hex[65];
        if (sscanf(line, "%zu %64s", &scalar, hex) != 2)
            continue;
        if (scalar >= 1 && scalar <= 8) {
            if (!parse_hex(&encoded[(scalar - 1) * 32], hex)) {
                fclose(file);
                return 0;
            }
            seen |= UINT8_C(1) << (scalar - 1);
        }
    }
    fclose(file);
    return seen == 0xff;
}

static int
load_scalar_fixtures(
    const char *path,
    scalar_fixture fixture[fixture_groups][8])
{
    FILE *file = fopen(path, "r");
    if (file == NULL)
        return 0;
    uint8_t seen[fixture_groups] = {0};
    char line[512];
    while (fgets(line, sizeof(line), file) != NULL) {
        if (line[0] == '#')
            continue;
        size_t group, lane, base;
        unsigned int negative;
        char scalar_hex[65], expected_hex[65];
        if (sscanf(line, "%zu %zu %zu %64s %u %64s",
                   &group, &lane, &base, scalar_hex, &negative,
                   expected_hex) != 6 ||
            group >= fixture_groups || lane >= 8 || base != lane + 1 ||
            negative > 1 ||
            !parse_hex(fixture[group][lane].scalar, scalar_hex) ||
            !parse_hex(fixture[group][lane].expected, expected_hex)) {
            fclose(file);
            return 0;
        }
        fixture[group][lane].negative = (uint8_t)negative;
        seen[group] |= UINT8_C(1) << lane;
    }
    fclose(file);
    for (size_t group = 0; group < fixture_groups; group++)
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
    uint64_t canonical_a[5], canonical_b[5];
    canonical_lane(canonical_a, a, lane);
    canonical_lane(canonical_b, b, lane);
    return memcmp(canonical_a, canonical_b, sizeof(canonical_a)) == 0;
}

static int
point_equal_projective(
    const narya_edwards_point_x8 *a,
    const narya_edwards_point_x8 *b)
{
    narya_r51x8 axbz, bxaz, aybz, byaz;
    narya_r51x8_mul_ifma(&axbz, &a->X, &b->Z);
    narya_r51x8_mul_ifma(&bxaz, &b->X, &a->Z);
    narya_r51x8_mul_ifma(&aybz, &a->Y, &b->Z);
    narya_r51x8_mul_ifma(&byaz, &b->Y, &a->Z);
    for (size_t lane = 0; lane < 8; lane++) {
        if (!field_equal_lane(&axbz, &bxaz, lane) ||
            !field_equal_lane(&aybz, &byaz, lane))
            return 0;
    }
    return 1;
}

static uint8_t
prepare_group(
    uint8_t scalar[8 * 32],
    uint8_t expected[8 * 32],
    const scalar_fixture fixture[8])
{
    uint8_t negative = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        memcpy(&scalar[lane * 32], fixture[lane].scalar, 32);
        memcpy(&expected[lane * 32], fixture[lane].expected, 32);
        negative |= fixture[lane].negative << lane;
    }
    return negative;
}

int
main(int argc, char **argv)
{
    if (argc != 3) {
        fprintf(stderr, "usage: %s BASEPOINT_FIXTURE SCALAR_FIXTURE\n", argv[0]);
        return 1;
    }
    const char *required = getenv("NARYA_REQUIRE_IFMA");
    if (!narya_r51x8_available()) {
        if (required != NULL && required[0] == '1') {
            fputs("AVX-512 IFMA required but unavailable\n", stderr);
            return 1;
        }
        puts("SKIP: AVX-512 IFMA unavailable");
        return 0;
    }

    uint8_t base_bytes[8 * 32] = {0};
    scalar_fixture fixture[fixture_groups][8] = {0};
    if (!load_basepoints(argv[1], base_bytes) ||
        !load_scalar_fixtures(argv[2], fixture)) {
        fputs("failed to load scalar-multiplication fixtures\n", stderr);
        return 1;
    }
    narya_edwards_point_x8 base;
    if (narya_edwards_decode_x8(&base, base_bytes, 0xff) != 0xff)
        return 1;
    narya_projective_niels_presigned_table_x8 table;
    narya_projective_niels_table_build_x8(&table, &base);

    for (size_t group = 0; group < fixture_groups; group++) {
        uint8_t scalar[8 * 32], expected_bytes[8 * 32];
        const uint8_t negative =
            prepare_group(scalar, expected_bytes, fixture[group]);
        narya_edwards_point_x8 got, expected;
        if (narya_variable_scalar_mult_x8(
                &got, &table, scalar, negative, 0xff) != 0xff ||
            narya_edwards_decode_x8(&expected, expected_bytes, 0xff) != 0xff ||
            !point_equal_projective(&got, &expected)) {
            fprintf(stderr, "full-width scalar multiplication mismatch group=%zu\n",
                    group);
            return 1;
        }

        /*
         * Compare the merged B10 schedule with the deliberately separate
         * [s]B + [-k]A construction. The two sides share field leaves but not
         * scalar recoding, fixed-base table shape, event order, or doubling
         * schedule.
         */
        uint8_t s[8 * 32];
        const size_t s_group = (group + 7) % fixture_groups;
        for (size_t lane = 0; lane < 8; lane++)
            memcpy(&s[lane * 32], fixture[s_group][lane].scalar, 32);
        narya_edwards_point_x8 a_term, b_term, separate, merged;
        if (narya_variable_scalar_mult_x8(
                &a_term, &table, scalar, 0xff, 0xff) != 0xff ||
            narya_fixed_base_scalar_mult_x8(&b_term, s, 0xff) != 0xff) {
            fprintf(stderr, "separate DSM preparation failed group=%zu\n", group);
            return 1;
        }
        narya_projective_niels_x8 a_cached;
        narya_edwards_to_projective_niels_x8(&a_cached, &a_term);
        narya_edwards_add_projective_niels_x8(
            &separate, &b_term, &a_cached);
        if (narya_asymmetric_fixed_b10_double_scalar_mult_x8(
                &merged, &table, s, scalar, 0xff) != 0xff ||
            !point_equal_projective(&merged, &separate)) {
            fprintf(stderr, "merged B10 DSM mismatch group=%zu\n", group);
            return 1;
        }
    }

    /* Masked lanes stay identities through all 250 doublings and additions. */
    uint8_t scalar[8 * 32], expected_bytes[8 * 32];
    uint8_t s[8 * 32];
    const uint8_t negative = prepare_group(scalar, expected_bytes, fixture[1]);
    for (size_t lane = 0; lane < 8; lane++)
        memcpy(&s[lane * 32], fixture[2][lane].scalar, 32);
    for (unsigned int active = 0; active <= 0xff; active++) {
        narya_edwards_point_x8 got, expected;
        if (narya_variable_scalar_mult_x8(
                &got, &table, scalar, negative, (uint8_t)active) !=
                (uint8_t)active ||
            narya_edwards_decode_x8(
                &expected, expected_bytes, (uint8_t)active) != (uint8_t)active ||
            !point_equal_projective(&got, &expected)) {
            fprintf(stderr, "active-mask scalar multiplication mismatch=%02x\n",
                    active);
            return 1;
        }

        narya_edwards_point_x8 a_term, b_term, separate, merged;
        const uint8_t active_mask = (uint8_t)active;
        if (narya_variable_scalar_mult_x8(
                &a_term, &table, scalar, active_mask, active_mask) !=
                active_mask ||
            narya_fixed_base_scalar_mult_x8(
                &b_term, s, active_mask) != active_mask) {
            fprintf(stderr, "active-mask separate DSM failed=%02x\n", active);
            return 1;
        }
        narya_projective_niels_x8 a_cached;
        narya_edwards_to_projective_niels_x8(&a_cached, &a_term);
        narya_edwards_add_projective_niels_x8(
            &separate, &b_term, &a_cached);
        if (narya_asymmetric_fixed_b10_double_scalar_mult_x8(
                &merged, &table, s, scalar, active_mask) != active_mask ||
            !point_equal_projective(&merged, &separate)) {
            fprintf(stderr, "active-mask merged B10 DSM mismatch=%02x\n", active);
            return 1;
        }
    }

    /* A noncanonical scalar invalidates only its own lane. */
    memcpy(&scalar[3 * 32], scalar_order, 32);
    narya_edwards_point_x8 got, expected;
    if (narya_variable_scalar_mult_x8(
            &got, &table, scalar, negative, 0xff) != 0xf7 ||
        narya_edwards_decode_x8(&expected, expected_bytes, 0xf7) != 0xf7 ||
        !point_equal_projective(&got, &expected)) {
        fputs("noncanonical scalar lane did not fail independently\n", stderr);
        return 1;
    }
    memcpy(&s[3 * 32], scalar_order, 32);
    if (narya_asymmetric_fixed_b10_double_scalar_mult_x8(
            &got, &table, s, scalar, 0xff) != 0xf7) {
        fputs("noncanonical B10 scalar lane did not fail independently\n", stderr);
        return 1;
    }
    puts("PASS: x8 variable-base scalar multiplication matches affine fixtures");
    return 0;
}
