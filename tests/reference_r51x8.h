/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#ifndef NARYA_REFERENCE_R51X8_H
#define NARYA_REFERENCE_R51X8_H

#include "narya_ed25519_asm.h"

static void
reference_r51x8_canonical_lane(uint64_t out[5], const narya_r51x8 *in, size_t lane)
{
    const uint64_t m = (UINT64_C(1) << 51) - 1;
    for (size_t limb = 0; limb < 5; limb++)
        out[limb] = in->limb[limb][lane];
    for (unsigned int round = 0; round < 4; round++) {
        for (size_t limb = 0; limb < 4; limb++) {
            const uint64_t carry = out[limb] >> 51;
            out[limb] &= m;
            out[limb + 1] += carry;
        }
        const uint64_t carry = out[4] >> 51;
        out[4] &= m;
        out[0] += 19 * carry;
    }
    if (out[1] == m && out[2] == m && out[3] == m && out[4] == m &&
        out[0] >= m - 18) {
        out[0] -= m - 18;
        out[1] = out[2] = out[3] = out[4] = 0;
    }
}

static int
reference_r51x8_equal_lane(
    const narya_r51x8 *a,
    const narya_r51x8 *b,
    size_t lane)
{
    uint64_t ca[5];
    uint64_t cb[5];
    reference_r51x8_canonical_lane(ca, a, lane);
    reference_r51x8_canonical_lane(cb, b, lane);
    uint64_t diff = 0;
    for (size_t limb = 0; limb < 5; limb++)
        diff |= ca[limb] ^ cb[limb];
    return diff == 0;
}

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

static void
reference_edwards_to_projective_niels_x8(
    narya_projective_niels_x8 *out,
    const narya_edwards_point_x8 *point)
{
    static const uint64_t two_d_limbs[5] = {
        UINT64_C(1859910466990425), UINT64_C(932731440258426),
        UINT64_C(1072319116312658), UINT64_C(1815898335770999),
        UINT64_C(633789495995903),
    };
    narya_r51x8 two_d;
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            two_d.limb[limb][lane] = two_d_limbs[limb];
    reference_r51x8_add(&out->Y_plus_X, &point->Y, &point->X);
    reference_r51x8_sub(&out->Y_minus_X, &point->Y, &point->X);
    out->Z = point->Z;
    reference_r51x8_mul(&out->T2d, &point->T, &two_d);
}

static void
reference_edwards_add_projective_niels_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point,
    const narya_projective_niels_x8 *cached)
{
    narya_r51x8 ymx, ypx, A, B, C, D, E, F, G, H;
    reference_r51x8_sub(&ymx, &point->Y, &point->X);
    reference_r51x8_add(&ypx, &point->Y, &point->X);
    reference_r51x8_mul(&A, &ymx, &cached->Y_minus_X);
    reference_r51x8_mul(&B, &ypx, &cached->Y_plus_X);
    reference_r51x8_mul(&C, &point->T, &cached->T2d);
    reference_r51x8_mul(&D, &point->Z, &cached->Z);
    reference_r51x8_add(&D, &D, &D);
    reference_r51x8_sub(&E, &B, &A);
    reference_r51x8_sub(&F, &D, &C);
    reference_r51x8_add(&G, &D, &C);
    reference_r51x8_add(&H, &B, &A);
    reference_r51x8_mul(&out->X, &E, &F);
    reference_r51x8_mul(&out->Y, &G, &H);
    reference_r51x8_mul(&out->T, &E, &H);
    reference_r51x8_mul(&out->Z, &F, &G);
}

#endif
