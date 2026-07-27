/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t random_state = UINT64_C(0x13ac957e4b682fd1);

static void
canonical_lane(uint64_t out[5], const narya_r51x8 *in, size_t lane)
{
    const uint64_t mask = (UINT64_C(1) << 51) - 1;
    for (size_t limb = 0; limb < 5; limb++)
        out[limb] = in->limb[limb][lane];
    for (size_t round = 0; round < 4; round++) {
        for (size_t limb = 0; limb < 4; limb++) {
            const uint64_t carry = out[limb] >> 51;
            out[limb] &= mask;
            out[limb + 1] += carry;
        }
        const uint64_t carry = out[4] >> 51;
        out[4] &= mask;
        out[0] += 19 * carry;
    }
    if (out[1] == mask && out[2] == mask && out[3] == mask &&
        out[4] == mask && out[0] >= mask - 18) {
        out[0] -= mask - 18;
        out[1] = out[2] = out[3] = out[4] = 0;
    }
}

static int
field_equal_lane(const narya_r51x8 *a, const narya_r51x8 *b, size_t lane)
{
    uint64_t canonical_a[5];
    uint64_t canonical_b[5];
    canonical_lane(canonical_a, a, lane);
    canonical_lane(canonical_b, b, lane);
    return memcmp(canonical_a, canonical_b, sizeof(canonical_a)) == 0;
}

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
tag(size_t lane, size_t sign, size_t entry, size_t limb, size_t coordinate)
{
    return UINT64_C(0x100000000) * (lane + 1) +
           UINT64_C(0x10000000) * sign +
           UINT64_C(0x00100000) * (entry + 1) +
           UINT64_C(0x00000100) * limb + coordinate + 1;
}

static uint64_t
selected_coordinate(
    const narya_projective_niels_x8 *point,
    size_t coordinate,
    size_t limb,
    size_t lane)
{
    switch (coordinate) {
    case 0: return point->Y_plus_X.limb[limb][lane];
    case 1: return point->Y_minus_X.limb[limb][lane];
    case 2: return point->Z.limb[limb][lane];
    default: return point->T2d.limb[limb][lane];
    }
}

static int
check_selector(void)
{
    narya_projective_niels_presigned_table_x8 table;
    for (size_t lane = 0; lane < 8; lane++)
        for (size_t sign = 0; sign < 2; sign++)
            for (size_t entry = 0; entry < 16; entry++)
                for (size_t limb = 0; limb < 5; limb++)
                    for (size_t coordinate = 0; coordinate < 4; coordinate++)
                        table.point[lane][sign][entry].limb[limb][coordinate] =
                            tag(lane, sign, entry, limb, coordinate);

    for (unsigned int active = 0; active <= 0xff; active++) {
        narya_radix32_round_x8 round = {0};
        for (size_t lane = 0; lane < 8; lane++) {
            round.magnitude[lane] = (uint8_t)(random64() % 16 + 1);
            if ((random64() & 1) != 0)
                round.nonzero_mask |= UINT8_C(1) << lane;
            if ((random64() & 1) != 0)
                round.negative_mask |= UINT8_C(1) << lane;
        }
        narya_projective_niels_x8 got;
        memset(&got, 0xa5, sizeof(got));
        narya_projective_niels_table_select_x8(
            &got, &table, &round, (uint8_t)active);
        const uint8_t lookup = round.nonzero_mask & (uint8_t)active;
        for (size_t lane = 0; lane < 8; lane++) {
            const uint8_t lane_mask = UINT8_C(1) << lane;
            for (size_t limb = 0; limb < 5; limb++) {
                for (size_t coordinate = 0; coordinate < 4; coordinate++) {
                    uint64_t want = 0;
                    if ((lookup & lane_mask) != 0) {
                        const size_t sign = (round.negative_mask >> lane) & 1u;
                        want = tag(lane, sign, round.magnitude[lane] - 1,
                                   limb, coordinate);
                    } else if (limb == 0 && coordinate < 3) {
                        want = 1;
                    }
                    if (selected_coordinate(&got, coordinate, limb, lane) != want) {
                        fprintf(stderr,
                            "selector mismatch active=%02x lane=%zu limb=%zu coordinate=%zu\n",
                            active, lane, limb, coordinate);
                        return 0;
                    }
                }
            }
        }
    }
    return 1;
}

static int
check_table_sign_pair(void)
{
    /* The identity is a valid point and makes every positive multiple equal. */
    narya_edwards_point_x8 base = {0};
    for (size_t lane = 0; lane < 8; lane++) {
        base.Y.limb[0][lane] = 1;
        base.Z.limb[0][lane] = 1;
    }
    narya_projective_niels_presigned_table_x8 table;
    memset(&table, 0xa5, sizeof(table));
    narya_projective_niels_table_build_x8(&table, &base);
    for (size_t lane = 0; lane < 8; lane++) {
        for (size_t entry = 0; entry < 16; entry++) {
            const narya_projective_niels_micro_entry_x8 *positive =
                &table.point[lane][0][entry];
            const narya_projective_niels_micro_entry_x8 *negative =
                &table.point[lane][1][entry];
            narya_r51x8 value[2][4] = {0};
            for (size_t coordinate = 0; coordinate < 4; coordinate++) {
                for (size_t limb = 0; limb < 5; limb++) {
                    value[0][coordinate].limb[limb][0] =
                        positive->limb[limb][coordinate];
                    value[1][coordinate].limb[limb][0] =
                        negative->limb[limb][coordinate];
                }
            }
            narya_r51x8 zero = {0};
            for (size_t sign = 0; sign < 2; sign++) {
                if (!field_equal_lane(&value[sign][0], &value[sign][1], 0) ||
                    !field_equal_lane(&value[sign][0], &value[sign][2], 0) ||
                    !field_equal_lane(&value[sign][3], &zero, 0)) {
                    fputs("identity table/sign construction mismatch\n", stderr);
                    return 0;
                }
            }
        }
    }
    return 1;
}

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
load_basepoint_vectors(const char *path, uint8_t encoded[129][32])
{
    FILE *file = fopen(path, "r");
    if (file == NULL)
        return 0;
    uint8_t seen[129] = {0};
    char line[256];
    while (fgets(line, sizeof(line), file) != NULL) {
        if (line[0] == '#')
            continue;
        size_t scalar = 0;
        char hex[65];
        if (sscanf(line, "%zu %64s", &scalar, hex) != 2 ||
            scalar == 0 || scalar > 128 || strlen(hex) != 64) {
            fclose(file);
            return 0;
        }
        for (size_t byte = 0; byte < 32; byte++) {
            const int high = hex_nibble(hex[2 * byte]);
            const int low = hex_nibble(hex[2 * byte + 1]);
            if (high < 0 || low < 0) {
                fclose(file);
                return 0;
            }
            encoded[scalar][byte] = (uint8_t)(high << 4 | low);
        }
        seen[scalar] = 1;
    }
    fclose(file);
    for (size_t scalar = 1; scalar <= 128; scalar++)
        if (seen[scalar] == 0)
            return 0;
    return 1;
}

static const narya_r51x8 *
niels_coordinate(const narya_projective_niels_x8 *point, size_t coordinate)
{
    switch (coordinate) {
    case 0: return &point->Y_plus_X;
    case 1: return &point->Y_minus_X;
    case 2: return &point->Z;
    default: return &point->T2d;
    }
}

static int
niels_equal_projective(
    const narya_projective_niels_x8 *a,
    const narya_projective_niels_x8 *b)
{
    for (size_t coordinate = 0; coordinate < 4; coordinate++) {
        narya_r51x8 left;
        narya_r51x8 right;
        narya_r51x8_mul_ifma(&left, niels_coordinate(a, coordinate), &b->Z);
        narya_r51x8_mul_ifma(&right, niels_coordinate(b, coordinate), &a->Z);
        for (size_t lane = 0; lane < 8; lane++)
            if (!field_equal_lane(&left, &right, lane))
                return 0;
    }
    return 1;
}

static int
check_table_group_law(const char *path)
{
    uint8_t vectors[129][32] = {{0}};
    if (!load_basepoint_vectors(path, vectors)) {
        fprintf(stderr, "failed to load basepoint fixture %s\n", path);
        return 0;
    }

    uint8_t encoded_base[8 * 32];
    for (size_t lane = 0; lane < 8; lane++)
        memcpy(&encoded_base[lane * 32], vectors[lane + 1], 32);
    narya_edwards_point_x8 base;
    if (narya_edwards_decode_x8(&base, encoded_base, 0xff) != 0xff)
        return 0;
    narya_projective_niels_presigned_table_x8 table;
    narya_projective_niels_table_build_x8(&table, &base);

    for (size_t magnitude = 1; magnitude <= 16; magnitude++) {
        uint8_t encoded_want[8 * 32];
        narya_radix32_round_x8 round = {
            .nonzero_mask = 0xff,
        };
        for (size_t lane = 0; lane < 8; lane++) {
            round.magnitude[lane] = (uint8_t)magnitude;
            memcpy(&encoded_want[lane * 32],
                   vectors[(lane + 1) * magnitude], 32);
        }

        narya_projective_niels_x8 selected;
        narya_projective_niels_table_select_x8(
            &selected, &table, &round, 0xff);
        narya_edwards_point_x8 expected_point;
        if (narya_edwards_decode_x8(&expected_point, encoded_want, 0xff) != 0xff)
            return 0;
        narya_projective_niels_x8 expected;
        narya_edwards_to_projective_niels_x8(&expected, &expected_point);
        if (!niels_equal_projective(&selected, &expected)) {
            fprintf(stderr, "positive table multiple mismatch magnitude=%zu\n",
                    magnitude);
            return 0;
        }

        round.negative_mask = 0xff;
        for (size_t lane = 0; lane < 8; lane++)
            encoded_want[lane * 32 + 31] ^= 0x80;
        narya_projective_niels_table_select_x8(
            &selected, &table, &round, 0xff);
        if (narya_edwards_decode_x8(&expected_point, encoded_want, 0xff) != 0xff)
            return 0;
        narya_edwards_to_projective_niels_x8(&expected, &expected_point);
        if (!niels_equal_projective(&selected, &expected)) {
            fprintf(stderr, "negative table multiple mismatch magnitude=%zu\n",
                    magnitude);
            return 0;
        }
    }
    return 1;
}

int
main(int argc, char **argv)
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
    if (argc != 2) {
        fprintf(stderr, "usage: %s BASEPOINT_FIXTURE\n", argv[0]);
        return 1;
    }
    if (!check_selector() || !check_table_sign_pair() ||
        !check_table_group_law(argv[1]))
        return 1;
    puts("PASS: pre-signed micro-AoS table, group law, and x8 transpose selector");
    return 0;
}
