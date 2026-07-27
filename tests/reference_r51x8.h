/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#ifndef NARYA_REFERENCE_R51X8_H
#define NARYA_REFERENCE_R51X8_H

#include "narya_ed25519_asm.h"

/*
 * Portable, deliberately differently expressed oracle for the IFMA leaf.
 * It models VPMADD52's low/high split with scalar __uint128_t arithmetic,
 * then performs the same mathematical rebase/fold/carry operations.  It does
 * not share assembly macros, register allocation or instruction scheduling.
 */
static void
reference_r51x8_mul(narya_r51x8 *out, const narya_r51x8 *x, const narya_r51x8 *y)
{
    const uint64_t mask52 = (UINT64_C(1) << 52) - 1;
    const uint64_t mask51 = (UINT64_C(1) << 51) - 1;

    for (size_t lane = 0; lane < NARYA_X8_LANES; lane++) {
        uint64_t low[9] = {0};
        uint64_t high[10] = {0};
        uint64_t folded[5];
        uint64_t carry[5];

        for (size_t i = 0; i < NARYA_R51_LIMBS; i++) {
            for (size_t j = 0; j < NARYA_R51_LIMBS; j++) {
                const __uint128_t p =
                    (__uint128_t)x->limb[i][lane] * y->limb[j][lane];
                low[i + j] += (uint64_t)p & mask52;
                high[i + j + 1] += (uint64_t)(p >> 52);
            }
        }

        for (size_t degree = 1; degree <= 8; degree++)
            low[degree] += high[degree] << 1;
        high[9] <<= 1;

        folded[0] = low[0] + 19 * low[5];
        folded[1] = low[1] + 19 * low[6];
        folded[2] = low[2] + 19 * low[7];
        folded[3] = low[3] + 19 * low[8];
        folded[4] = low[4] + 19 * high[9];

        for (size_t i = 0; i < 5; i++)
            carry[i] = folded[i] >> 51;
        out->limb[0][lane] = (folded[0] & mask51) + 19 * carry[4];
        out->limb[1][lane] = (folded[1] & mask51) + carry[0];
        out->limb[2][lane] = (folded[2] & mask51) + carry[1];
        out->limb[3][lane] = (folded[3] & mask51) + carry[2];
        out->limb[4][lane] = (folded[4] & mask51) + carry[3];
    }
}

static void
reference_r51x8_normalize(narya_r51x8 *out, uint64_t raw[5][8])
{
    const uint64_t mask51 = (UINT64_C(1) << 51) - 1;
    for (size_t lane = 0; lane < 8; lane++) {
        uint64_t carry[5];
        for (size_t limb = 0; limb < 5; limb++)
            carry[limb] = raw[limb][lane] >> 51;
        out->limb[0][lane] = (raw[0][lane] & mask51) + 19 * carry[4];
        out->limb[1][lane] = (raw[1][lane] & mask51) + carry[0];
        out->limb[2][lane] = (raw[2][lane] & mask51) + carry[1];
        out->limb[3][lane] = (raw[3][lane] & mask51) + carry[2];
        out->limb[4][lane] = (raw[4][lane] & mask51) + carry[3];
    }
}

static void
reference_r51x8_add(narya_r51x8 *out, const narya_r51x8 *x, const narya_r51x8 *y)
{
    uint64_t raw[5][8];
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            raw[limb][lane] = x->limb[limb][lane] + y->limb[limb][lane];
    reference_r51x8_normalize(out, raw);
}

static void
reference_r51x8_sub(narya_r51x8 *out, const narya_r51x8 *x, const narya_r51x8 *y)
{
    const uint64_t bias[5] = {
        UINT64_C(0x001fffffffffffb4),
        UINT64_C(0x001ffffffffffffc), UINT64_C(0x001ffffffffffffc),
        UINT64_C(0x001ffffffffffffc), UINT64_C(0x001ffffffffffffc),
    };
    uint64_t raw[5][8];
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            raw[limb][lane] = x->limb[limb][lane] + bias[limb] - y->limb[limb][lane];
    reference_r51x8_normalize(out, raw);
}

static void
reference_r51x8_neg(narya_r51x8 *out, const narya_r51x8 *x)
{
    narya_r51x8 zero = {0};
    reference_r51x8_sub(out, &zero, x);
}

static void
reference_edwards_double_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point)
{
    narya_r51x8 A, B, C, D, E, F, G, H;
    reference_r51x8_mul(&A, &point->X, &point->X);
    reference_r51x8_mul(&B, &point->Y, &point->Y);
    reference_r51x8_mul(&C, &point->Z, &point->Z);
    reference_r51x8_add(&C, &C, &C);
    reference_r51x8_mul(&E, &point->X, &point->Y);
    reference_r51x8_add(&E, &E, &E);
    reference_r51x8_neg(&D, &A);
    reference_r51x8_add(&G, &D, &B);
    reference_r51x8_sub(&F, &G, &C);
    reference_r51x8_sub(&H, &D, &B);
    reference_r51x8_mul(&out->X, &E, &F);
    reference_r51x8_mul(&out->Y, &G, &H);
    reference_r51x8_mul(&out->T, &E, &H);
    reference_r51x8_mul(&out->Z, &F, &G);
}

#endif
