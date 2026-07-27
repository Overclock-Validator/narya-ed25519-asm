/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t random_state = UINT64_C(0x13ac957e4b682fd1);

static void
canonical_lane(uint64_t out[5], const narya_r51x8 *in)
{
    const uint64_t mask = (UINT64_C(1) << 51) - 1;
    for (size_t limb = 0; limb < 5; limb++)
        out[limb] = in->limb[limb][0];
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
field_equal(const narya_r51x8 *a, const narya_r51x8 *b)
{
    uint64_t canonical_a[5];
    uint64_t canonical_b[5];
    canonical_lane(canonical_a, a);
    canonical_lane(canonical_b, b);
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
                if (!field_equal(&value[sign][0], &value[sign][1]) ||
                    !field_equal(&value[sign][0], &value[sign][2]) ||
                    !field_equal(&value[sign][3], &zero)) {
                    fputs("identity table/sign construction mismatch\n", stderr);
                    return 0;
                }
            }
        }
    }
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
    if (!check_selector() || !check_table_sign_pair())
        return 1;
    puts("PASS: pre-signed micro-AoS table and x8 transpose selector");
    return 0;
}
