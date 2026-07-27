/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "narya_ed25519_asm.h"
#include "internal.h"
#include "reference_r51x8.h"

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

static uint64_t random_state = UINT64_C(0xd1b54a32d192ed03);

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
equal(const narya_r51x8 *a, const narya_r51x8 *b)
{
    return memcmp(a, b, sizeof(*a)) == 0;
}

static int
point_equal_exact(const narya_edwards_point_x8 *a, const narya_edwards_point_x8 *b)
{
    return equal(&a->X, &b->X) && equal(&a->Y, &b->Y) &&
           equal(&a->Z, &b->Z) && equal(&a->T, &b->T);
}

static void
broadcast_limbs(narya_r51x8 *out, const uint64_t limbs[5])
{
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            out->limb[limb][lane] = limbs[limb];
}

static int
check_point_doubling(void)
{
    static const uint64_t base_x[5] = {
        UINT64_C(1738742601995546), UINT64_C(1146398526822698),
        UINT64_C(2070867633025821), UINT64_C(562264141797630),
        UINT64_C(587772402128613),
    };
    static const uint64_t base_y[5] = {
        UINT64_C(1801439850948184), UINT64_C(1351079888211148),
        UINT64_C(450359962737049), UINT64_C(900719925474099),
        UINT64_C(1801439850948198),
    };
    static const uint64_t one[5] = {1, 0, 0, 0, 0};
    static const uint64_t base_t[5] = {
        UINT64_C(1841354044333475), UINT64_C(16398895984059),
        UINT64_C(755974180946558), UINT64_C(900171276175154),
        UINT64_C(1821297809914039),
    };
    narya_edwards_point_x8 got;
    narya_edwards_point_x8 want;
    narya_edwards_point_x8 state;
    broadcast_limbs(&state.X, base_x);
    broadcast_limbs(&state.Y, base_y);
    broadcast_limbs(&state.Z, one);
    broadcast_limbs(&state.T, base_t);

    for (size_t step = 0; step < 256; step++) {
        reference_edwards_double_x8(&want, &state);
        narya_edwards_double_x8(&got, &state);
        if (!point_equal_exact(&got, &want)) {
            fprintf(stderr, "point-double mismatch at step %zu\n", step);
            return 0;
        }
        narya_edwards_double_x8(&state, &state);
        if (!point_equal_exact(&state, &want)) {
            fprintf(stderr, "in-place point-double mismatch at step %zu\n", step);
            return 0;
        }
    }
    return 1;
}

static void
dump_mismatch(const narya_r51x8 *got, const narya_r51x8 *want)
{
    for (size_t limb = 0; limb < NARYA_R51_LIMBS; limb++) {
        for (size_t lane = 0; lane < NARYA_X8_LANES; lane++) {
            if (got->limb[limb][lane] != want->limb[limb][lane]) {
                fprintf(stderr,
                    "mismatch limb=%zu lane=%zu got=%016" PRIx64
                    " want=%016" PRIx64 "\n",
                    limb, lane, got->limb[limb][lane],
                    want->limb[limb][lane]);
                return;
            }
        }
    }
}

static int
check_case(const narya_r51x8 *x, const narya_r51x8 *y)
{
    narya_r51x8 got;
    narya_r51x8 want;
    reference_r51x8_mul(&want, x, y);
    if (narya_r51x8_mul(&got, x, y) != NARYA_OK)
        return 0;
    if (!equal(&got, &want)) {
        dump_mismatch(&got, &want);
        return 0;
    }

    /* Alias contracts are checked independently for both source positions. */
    narya_r51x8 alias = *x;
    if (narya_r51x8_mul(&alias, &alias, y) != NARYA_OK || !equal(&alias, &want))
        return 0;
    alias = *y;
    if (narya_r51x8_mul(&alias, x, &alias) != NARYA_OK || !equal(&alias, &want))
        return 0;

    reference_r51x8_add(&want, x, y);
    if (narya_r51x8_add(&got, x, y) != NARYA_OK || !equal(&got, &want))
        return 0;
    alias = *x;
    if (narya_r51x8_add(&alias, &alias, y) != NARYA_OK || !equal(&alias, &want))
        return 0;
    alias = *y;
    if (narya_r51x8_add(&alias, x, &alias) != NARYA_OK || !equal(&alias, &want))
        return 0;

    reference_r51x8_sub(&want, x, y);
    if (narya_r51x8_sub(&got, x, y) != NARYA_OK || !equal(&got, &want))
        return 0;
    alias = *x;
    if (narya_r51x8_sub(&alias, &alias, y) != NARYA_OK || !equal(&alias, &want))
        return 0;
    alias = *y;
    if (narya_r51x8_sub(&alias, x, &alias) != NARYA_OK || !equal(&alias, &want))
        return 0;

    reference_r51x8_neg(&want, x);
    if (narya_r51x8_neg(&got, x) != NARYA_OK || !equal(&got, &want))
        return 0;
    alias = *x;
    if (narya_r51x8_neg(&alias, &alias) != NARYA_OK || !equal(&alias, &want))
        return 0;
    return 1;
}

int
main(void)
{
    if (!narya_r51x8_available()) {
        puts("SKIP: full AVX-512 IFMA feature set is unavailable");
        return 77;
    }

    narya_r51x8 x = {0};
    narya_r51x8 y = {0};
    if (!check_case(&x, &y))
        return 1;

    /* Maximum legal composable limbs exercise every proven upper bound. */
    for (size_t limb = 0; limb < NARYA_R51_LIMBS; limb++) {
        for (size_t lane = 0; lane < NARYA_X8_LANES; lane++) {
            x.limb[limb][lane] = (UINT64_C(1) << 52) - 1;
            y.limb[limb][lane] = (UINT64_C(1) << 52) - 1 - lane;
        }
    }
    if (!check_case(&x, &y))
        return 1;

    for (size_t iteration = 0; iteration < 10000; iteration++) {
        for (size_t limb = 0; limb < NARYA_R51_LIMBS; limb++) {
            for (size_t lane = 0; lane < NARYA_X8_LANES; lane++) {
                x.limb[limb][lane] = random64() & ((UINT64_C(1) << 52) - 1);
                y.limb[limb][lane] = random64() & ((UINT64_C(1) << 52) - 1);
            }
        }
        if (!check_case(&x, &y)) {
            fprintf(stderr, "failed random iteration %zu\n", iteration);
            return 1;
        }
    }

    narya_r51x8 unchanged = x;
    x.limb[2][5] = UINT64_C(1) << 52;
    if (narya_r51x8_mul(&unchanged, &x, &y) != NARYA_ERR_RANGE) {
        fputs("out-of-range input was not rejected\n", stderr);
        return 1;
    }

    if (!check_point_doubling())
        return 1;

    puts("PASS: r51x8 field and point-double operations match scalar oracles");
    return 0;
}
