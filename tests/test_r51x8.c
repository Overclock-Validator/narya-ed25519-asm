/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "narya_ed25519_asm.h"
#include "internal.h"
#include "reference_r51x8.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
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

static void
copy_point_lane(
    narya_edwards_point_x8 *out,
    size_t out_lane,
    const narya_edwards_point_x8 *in,
    size_t in_lane)
{
    for (size_t limb = 0; limb < 5; limb++) {
        out->X.limb[limb][out_lane] = in->X.limb[limb][in_lane];
        out->Y.limb[limb][out_lane] = in->Y.limb[limb][in_lane];
        out->Z.limb[limb][out_lane] = in->Z.limb[limb][in_lane];
        out->T.limb[limb][out_lane] = in->T.limb[limb][in_lane];
    }
}

static void
set_point_lane(
    narya_edwards_point_x8 *out,
    size_t lane,
    const uint64_t x[5],
    const uint64_t y[5],
    const uint64_t z[5],
    const uint64_t t[5])
{
    for (size_t limb = 0; limb < 5; limb++) {
        out->X.limb[limb][lane] = x[limb];
        out->Y.limb[limb][lane] = y[limb];
        out->Z.limb[limb][lane] = z[limb];
        out->T.limb[limb][lane] = t[limb];
    }
}

static int
point_equal_modp_lane(
    const narya_edwards_point_x8 *a,
    const narya_edwards_point_x8 *b,
    size_t lane)
{
    return reference_r51x8_equal_lane(&a->X, &b->X, lane) &&
           reference_r51x8_equal_lane(&a->Y, &b->Y, lane) &&
           reference_r51x8_equal_lane(&a->Z, &b->Z, lane) &&
           reference_r51x8_equal_lane(&a->T, &b->T, lane);
}

static int
check_decode(void)
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
    static const uint64_t base_t[5] = {
        UINT64_C(1841354044333475), UINT64_C(16398895984059),
        UINT64_C(755974180946558), UINT64_C(900171276175154),
        UINT64_C(1821297809914039),
    };
    static const uint64_t sqrt_m1[5] = {
        UINT64_C(1718705420411056), UINT64_C(234908883556509),
        UINT64_C(2233514472574048), UINT64_C(2117202627021982),
        UINT64_C(765476049583133),
    };
    static const uint64_t zero[5] = {0, 0, 0, 0, 0};
    static const uint64_t one[5] = {1, 0, 0, 0, 0};

    uint8_t encoded[8 * 32] = {0};
    encoded[0 * 32 + 0] = 0x58;
    for (size_t i = 1; i < 32; i++)
        encoded[0 * 32 + i] = 0x66; /* canonical basepoint */
    encoded[1 * 32 + 0] = 1;       /* identity */
    encoded[2 * 32 + 0] = 1;
    encoded[2 * 32 + 31] = 0x80;   /* permissive negative-zero identity */
    encoded[3 * 32 + 0] = 0xee;
    for (size_t i = 1; i < 31; i++)
        encoded[3 * 32 + i] = 0xff;
    encoded[3 * 32 + 31] = 0x7f;   /* p+1, noncanonical identity alias */
    memcpy(&encoded[4 * 32], &encoded[3 * 32], 32);
    encoded[4 * 32 + 31] = 0xff;   /* p+1 with sign one */
    encoded[5 * 32 + 0] = 0xed;
    for (size_t i = 1; i < 31; i++)
        encoded[5 * 32 + i] = 0xff;
    encoded[5 * 32 + 31] = 0x7f;   /* p -> y=0, x=sqrt(-1) */
    memcpy(&encoded[6 * 32], &encoded[0 * 32], 32);
    encoded[6 * 32 + 31] |= 0x80;  /* negative basepoint x */
    encoded[7 * 32 + 0] = 2;       /* nonsquare ratio: invalid compressed point */

    narya_edwards_point_x8 got;
    const uint8_t valid = narya_edwards_decode_x8(&got, encoded, 0xff);
    if (valid != 0x7f) {
        fprintf(stderr, "decode mask=%02x want=7f\n", valid);
        return 0;
    }

    narya_edwards_point_x8 want = {0};
    set_point_lane(&want, 0, base_x, base_y, one, base_t);
    for (size_t lane = 1; lane <= 4; lane++)
        set_point_lane(&want, lane, zero, one, one, zero);
    set_point_lane(&want, 5, sqrt_m1, zero, one, zero);

    narya_r51x8 bx, neg_bx, bt, neg_bt;
    broadcast_limbs(&bx, base_x);
    broadcast_limbs(&bt, base_t);
    reference_r51x8_neg(&neg_bx, &bx);
    reference_r51x8_neg(&neg_bt, &bt);
    uint64_t neg_x[5], neg_t[5];
    for (size_t limb = 0; limb < 5; limb++) {
        neg_x[limb] = neg_bx.limb[limb][0];
        neg_t[limb] = neg_bt.limb[limb][0];
    }
    set_point_lane(&want, 6, neg_x, base_y, one, neg_t);
    set_point_lane(&want, 7, zero, one, one, zero);

    for (size_t lane = 0; lane < 8; lane++) {
        if (!point_equal_modp_lane(&got, &want, lane)) {
            fprintf(stderr, "decoded point mismatch in lane %zu\n", lane);
            return 0;
        }
    }

    /* Every inactive lane is identity and cannot retain prior output state. */
    memset(&got, 0xa5, sizeof(got));
    if (narya_edwards_decode_x8(&got, encoded, 0) != 0)
        return 0;
    narya_edwards_point_x8 identity = {0};
    for (size_t lane = 0; lane < 8; lane++)
        set_point_lane(&identity, lane, zero, one, one, zero);
    for (size_t lane = 0; lane < 8; lane++)
        if (!point_equal_modp_lane(&got, &identity, lane))
            return 0;
    return 1;
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

    narya_edwards_point_x8 heterogeneous = {0};
    for (size_t step = 0; step < 256; step++) {
        if (step < 8)
            copy_point_lane(&heterogeneous, step, &state, 0);
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

    /*
     * Every lane now holds a different power-of-two multiple. Add a cached
     * copy of that same lane and compare both ordinary and in-place paths.
     */
    narya_projective_niels_x8 cached;
    narya_projective_niels_x8 cached_ref;
    narya_edwards_to_projective_niels_x8(&cached, &heterogeneous);
    reference_edwards_to_projective_niels_x8(&cached_ref, &heterogeneous);
    if (memcmp(&cached, &cached_ref, sizeof(cached)) != 0) {
        fputs("projective-Niels conversion mismatch\n", stderr);
        return 0;
    }
    reference_edwards_add_projective_niels_x8(&want, &heterogeneous, &cached_ref);
    narya_edwards_add_projective_niels_x8(&got, &heterogeneous, &cached);
    if (!point_equal_exact(&got, &want)) {
        fputs("heterogeneous projective-Niels addition mismatch\n", stderr);
        return 0;
    }
    narya_edwards_add_projective_niels_x8(&heterogeneous, &heterogeneous, &cached);
    if (!point_equal_exact(&heterogeneous, &want)) {
        fputs("in-place projective-Niels addition mismatch\n", stderr);
        return 0;
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
    for (size_t lane = 0; lane < NARYA_X8_LANES; lane++) {
        uint64_t got_canonical[5];
        uint64_t want_canonical[5];
        narya_r51x8_canonical_lane(got_canonical, x, lane);
        reference_r51x8_canonical_lane(want_canonical, x, lane);
        if (memcmp(got_canonical, want_canonical, sizeof(got_canonical)) != 0) {
            fprintf(stderr, "canonicalization mismatch lane=%zu\n", lane);
            return 0;
        }
    }

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

static int
check_repeated_squares(const narya_r51x8 *input)
{
    static const unsigned int counts[] = {0, 1, 2, 5, 10, 20, 50, 100, 252};

    for (size_t count_index = 0;
         count_index < sizeof(counts) / sizeof(counts[0]);
         count_index++) {
        const unsigned int count = counts[count_index];
        narya_r51x8 want = *input;
        for (unsigned int square = 0; square < count; square++) {
            narya_r51x8 next;
            reference_r51x8_mul(&next, &want, &want);
            want = next;
        }

        narya_r51x8 got;
        narya_r51x8_repeated_square_ifma(&got, input, count);
        if (!equal(&got, &want)) {
            fprintf(stderr, "repeated-square mismatch at count=%u\n", count);
            dump_mismatch(&got, &want);
            return 0;
        }

        got = *input;
        narya_r51x8_repeated_square_ifma(&got, &got, count);
        if (!equal(&got, &want)) {
            fprintf(stderr,
                "in-place repeated-square mismatch at count=%u\n", count);
            dump_mismatch(&got, &want);
            return 0;
        }
    }
    return 1;
}

int
main(void)
{
    if (!narya_r51x8_available()) {
        if (getenv("NARYA_REQUIRE_IFMA") != NULL) {
            fputs("FAIL: native IFMA execution was required but unavailable\n", stderr);
            return 1;
        }
        puts("SKIP: full AVX-512 IFMA feature set is unavailable");
        return 0;
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
    if (!check_repeated_squares(&x))
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
        if (iteration < 64 && !check_repeated_squares(&x)) {
            fprintf(stderr,
                "failed repeated-square random iteration %zu\n", iteration);
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
    if (!check_decode())
        return 1;

    puts("PASS: r51x8 field, point, and permissive decode gates passed");
    return 0;
}
