/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Permissive eight-lane Edwards25519 decompression over the native r51 field
 * leaves.  This file is intentionally C orchestration: decoder policy is
 * consensus-visible, and keeping each decision explicit makes it possible to
 * differential-test the byte semantics before fusing schedules in assembly.
 *
 * The algebra follows the Narya source at
 * eff4c8ddafdfe0448eb50f2eafc723a42b95fe2c.  See the decoder item in
 * docs/proofs/FORMALIZATION_BACKLOG.md for the intended machine-checked split.
 */
#include "internal.h"

#include <string.h>

static const uint64_t mask51 = (UINT64_C(1) << 51) - 1;

static const uint64_t curve_d[5] = {
    UINT64_C(929955233495203), UINT64_C(466365720129213),
    UINT64_C(1662059464998953), UINT64_C(2033849074728123),
    UINT64_C(1442794654840575),
};

static const uint64_t sqrt_m1[5] = {
    UINT64_C(1718705420411056), UINT64_C(234908883556509),
    UINT64_C(2233514472574048), UINT64_C(2117202627021982),
    UINT64_C(765476049583133),
};

static uint64_t
load64_le(const uint8_t *p)
{
    uint64_t value = 0;
    for (unsigned int i = 0; i < 8; i++)
        value |= (uint64_t)p[i] << (8 * i);
    return value;
}

static void
broadcast(narya_r51x8 *out, const uint64_t limbs[5])
{
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            out->limb[limb][lane] = limbs[limb];
}

static void
set_one(narya_r51x8 *out)
{
    memset(out, 0, sizeof(*out));
    for (size_t lane = 0; lane < 8; lane++)
        out->limb[0][lane] = 1;
}

static void
decode_y(narya_r51x8 *out, const uint8_t encoded[8 * 32], uint8_t active)
{
    memset(out, 0, sizeof(*out));
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) == 0) {
            out->limb[0][lane] = 1;
            continue;
        }

        /*
         * Parse the low 255 bits directly into radix-2^51 limbs.  With
         * r<2^255 and p=2^255-19, the only non-canonical values are p..p+18.
         * They have upper limbs all B-1 and reduce to 0..18 in limb zero.
         */
        const uint8_t *lane_bytes = &encoded[lane * 32];
        const uint64_t w0 = load64_le(&lane_bytes[0]);
        const uint64_t w1 = load64_le(&lane_bytes[8]);
        const uint64_t w2 = load64_le(&lane_bytes[16]);
        const uint64_t w3 = load64_le(&lane_bytes[24]) &
                            UINT64_C(0x7fffffffffffffff);
        uint64_t limbs[5];
        limbs[0] = w0 & mask51;
        limbs[1] = ((w0 >> 51) | (w1 << 13)) & mask51;
        limbs[2] = ((w1 >> 38) | (w2 << 26)) & mask51;
        limbs[3] = ((w2 >> 25) | (w3 << 39)) & mask51;
        limbs[4] = (w3 >> 12) & mask51;

        if (limbs[1] == mask51 && limbs[2] == mask51 &&
            limbs[3] == mask51 && limbs[4] == mask51 &&
            limbs[0] >= mask51 - 18) {
            limbs[0] -= mask51 - 18; /* subtract p's limb 0, B-19 */
            limbs[1] = limbs[2] = limbs[3] = limbs[4] = 0;
        }
        for (size_t limb = 0; limb < 5; limb++)
            out->limb[limb][lane] = limbs[limb];
    }
}

static void
canonicalize_lane(uint64_t out[5], const narya_r51x8 *in, size_t lane)
{
    for (size_t i = 0; i < 5; i++)
        out[i] = in->limb[i][lane];

    /* Four sequential passes are sufficient from the composable u52 domain. */
    for (unsigned int round = 0; round < 4; round++) {
        for (size_t i = 0; i < 4; i++) {
            const uint64_t carry = out[i] >> 51;
            out[i] &= mask51;
            out[i + 1] += carry;
        }
        const uint64_t carry = out[4] >> 51;
        out[4] &= mask51;
        out[0] += 19 * carry;
    }

    /* Now 0 <= value < 2^255=p+19; only p..p+18 need subtraction. */
    if (out[1] == mask51 && out[2] == mask51 && out[3] == mask51 &&
        out[4] == mask51 && out[0] >= mask51 - 18) {
        out[0] -= mask51 - 18;
        out[1] = out[2] = out[3] = out[4] = 0;
    }
}

static uint8_t
equal_mask(const narya_r51x8 *x, const narya_r51x8 *y)
{
    uint8_t mask = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        uint64_t a[5];
        uint64_t b[5];
        canonicalize_lane(a, x, lane);
        canonicalize_lane(b, y, lane);
        uint64_t diff = 0;
        for (size_t limb = 0; limb < 5; limb++)
            diff |= a[limb] ^ b[limb];
        if (diff == 0)
            mask |= UINT8_C(1) << lane;
    }
    return mask;
}

static uint8_t
negative_mask(const narya_r51x8 *x)
{
    uint8_t mask = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        uint64_t canonical[5];
        canonicalize_lane(canonical, x, lane);
        mask |= (uint8_t)(canonical[0] & 1) << lane;
    }
    return mask;
}

static void
select_lanes(narya_r51x8 *out, const narya_r51x8 *a, const narya_r51x8 *b, uint8_t b_mask)
{
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            out->limb[limb][lane] =
                (b_mask & (UINT8_C(1) << lane)) != 0
                    ? b->limb[limb][lane]
                    : a->limb[limb][lane];
}

static void
repeated_square_multiply(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *multiplier,
    unsigned int count)
{
    narya_r51x8 value = *x;
    for (unsigned int i = 0; i < count; i++)
        narya_r51x8_mul_ifma(&value, &value, &value);
    narya_r51x8_mul_ifma(out, &value, multiplier);
}

/* z = x^(2^252-3), the standard pow22523 addition chain. */
static void
pow22523(narya_r51x8 *z, const narya_r51x8 *x)
{
    const narya_r51x8 base = *x;
    narya_r51x8 x2, x9, x11, x5, x10, x20, x40;
    narya_r51x8 x50, x100, x200, x250;
    narya_r51x8_mul_ifma(&x2, &base, &base);
    repeated_square_multiply(&x9, &x2, &base, 2);
    narya_r51x8_mul_ifma(&x11, &x9, &x2);
    repeated_square_multiply(&x5, &x11, &x9, 1);
    repeated_square_multiply(&x10, &x5, &x5, 5);
    repeated_square_multiply(&x20, &x10, &x10, 10);
    repeated_square_multiply(&x40, &x20, &x20, 20);
    repeated_square_multiply(&x50, &x40, &x10, 10);
    repeated_square_multiply(&x100, &x50, &x50, 50);
    repeated_square_multiply(&x200, &x100, &x100, 100);
    repeated_square_multiply(&x250, &x200, &x50, 50);
    repeated_square_multiply(z, &x250, &base, 2);
}

static uint8_t
sqrt_ratio(narya_r51x8 *out, const narya_r51x8 *u, const narya_r51x8 *v)
{
    narya_r51x8 uv, power, root, root2, check, neg_u;
    narya_r51x8 root_i, neg_ui, root_times_i;
    broadcast(&root_i, sqrt_m1);
    narya_r51x8_mul_ifma(&uv, u, v);
    pow22523(&power, &uv);
    narya_r51x8_mul_ifma(&root, u, &power);
    narya_r51x8_mul_ifma(&root2, &root, &root);
    narya_r51x8_mul_ifma(&check, v, &root2);
    narya_r51x8_neg_ifma(&neg_u, u);
    narya_r51x8_mul_ifma(&neg_ui, &neg_u, &root_i);

    const uint8_t correct = equal_mask(&check, u);
    const uint8_t flipped = equal_mask(&check, &neg_u);
    const uint8_t flipped_i = equal_mask(&check, &neg_ui);
    narya_r51x8_mul_ifma(&root_times_i, &root, &root_i);
    select_lanes(&root, &root, &root_times_i, flipped | flipped_i);

    /* The decoder's preferred root is the nonnegative canonical root. */
    narya_r51x8_neg_ifma(&neg_u, &root);
    select_lanes(&root, &root, &neg_u, negative_mask(&root));
    *out = root;
    return correct | flipped;
}

uint8_t
narya_edwards_decode_x8(
    narya_edwards_point_x8 *out,
    const uint8_t encoded[8 * 32],
    uint8_t active)
{
    narya_r51x8 y, y2, one, d, u, v, x, neg_x, t, zero = {0};
    decode_y(&y, encoded, active);
    set_one(&one);
    broadcast(&d, curve_d);
    narya_r51x8_mul_ifma(&y2, &y, &y);
    narya_r51x8_sub_ifma(&u, &y2, &one);
    narya_r51x8_mul_ifma(&v, &y2, &d);
    narya_r51x8_add_ifma(&v, &v, &one);
    uint8_t valid = sqrt_ratio(&x, &u, &v) & active;

    uint8_t requested_sign = 0;
    for (size_t lane = 0; lane < 8; lane++)
        requested_sign |= (encoded[lane * 32 + 31] >> 7) << lane;
    const uint8_t change_sign = (negative_mask(&x) ^ requested_sign) & active;
    narya_r51x8_neg_ifma(&neg_x, &x);
    select_lanes(&x, &x, &neg_x, change_sign);
    narya_r51x8_mul_ifma(&t, &x, &y);

    /* Invalid and inactive lanes become the identity (0,1,1,0). */
    select_lanes(&out->X, &zero, &x, valid);
    select_lanes(&out->Y, &one, &y, valid);
    out->Z = one;
    select_lanes(&out->T, &zero, &t, valid);
    return valid;
}
