/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Audit-oriented C coordination over bounded native assembly stages. Hot
 * doubling and Niels linear layers are fused only through one carry boundary;
 * final coordinate products stay explicit and profiler-visible. This keeps
 * each formula boundary independently inspectable instead of hiding a whole
 * scalar-multiplication round in one opaque assembly symbol.
 * See docs/architecture/PORTING_PLAN.md and docs/proofs/R51_FIELD_CONTRACT.md.
 */
#include "internal.h"

#include <string.h>

/* Reduced radix-2^51 representation of 2d for Edwards25519. */
static const uint64_t narya_curve_2d[5] = {
    UINT64_C(1859910466990425), UINT64_C(932731440258426),
    UINT64_C(1072319116312658), UINT64_C(1815898335770999),
    UINT64_C(633789495995903),
};

static void
narya_broadcast_r51x8(narya_r51x8 *out, const uint64_t limbs[5])
{
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t lane = 0; lane < 8; lane++)
            out->limb[limb][lane] = limbs[limb];
}

/*
 * The native Stage-2 leaf forms [E,F,G,H] from raw products with one carry
 * layer. The four final products remain separate, independently tested field
 * leaves. This boundary mirrors the current Go backend without turning the
 * whole point formula into one opaque assembly monolith; see
 * docs/proofs/R51_FIELD_CONTRACT.md and docs/architecture/PORTING_PLAN.md.
 */

void
narya_edwards_double_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point)
{
    narya_double_stage2_workspace_x8 stage2;
    narya_r51x8_double_stage2_ifma(
        &stage2, &point->X, &point->Y, &point->Z);

    /* All input coordinates are dead here, so exact out==point is safe. */
    narya_r51x8_mul_ifma(&out->X, &stage2.slot[0], &stage2.slot[1]);
    narya_r51x8_mul_ifma(&out->Y, &stage2.slot[2], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->T, &stage2.slot[0], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->Z, &stage2.slot[1], &stage2.slot[2]);
}

void
narya_edwards_double_to_projective_x8(
    narya_projective_point_x8 *out,
    const narya_edwards_point_x8 *point)
{
    narya_double_stage2_workspace_x8 stage2;
    narya_r51x8_double_stage2_ifma(
        &stage2, &point->X, &point->Y, &point->Z);
    narya_r51x8_mul_ifma(&out->X, &stage2.slot[0], &stage2.slot[1]);
    narya_r51x8_mul_ifma(&out->Y, &stage2.slot[2], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->Z, &stage2.slot[1], &stage2.slot[2]);
}

void
narya_projective_double_x8(
    narya_projective_point_x8 *out,
    const narya_projective_point_x8 *point)
{
    narya_double_stage2_workspace_x8 stage2;
    narya_r51x8_double_stage2_ifma(
        &stage2, &point->X, &point->Y, &point->Z);
    narya_r51x8_mul_ifma(&out->X, &stage2.slot[0], &stage2.slot[1]);
    narya_r51x8_mul_ifma(&out->Y, &stage2.slot[2], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->Z, &stage2.slot[1], &stage2.slot[2]);
}

void
narya_projective_double_to_edwards_x8(
    narya_edwards_point_x8 *out,
    const narya_projective_point_x8 *point)
{
    narya_double_stage2_workspace_x8 stage2;
    narya_r51x8_double_stage2_ifma(
        &stage2, &point->X, &point->Y, &point->Z);
    narya_r51x8_mul_ifma(&out->X, &stage2.slot[0], &stage2.slot[1]);
    narya_r51x8_mul_ifma(&out->Y, &stage2.slot[2], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->T, &stage2.slot[0], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->Z, &stage2.slot[1], &stage2.slot[2]);
}

void
narya_edwards_to_projective_niels_x8(
    narya_projective_niels_x8 *out,
    const narya_edwards_point_x8 *point)
{
    narya_r51x8 two_d;
    narya_broadcast_r51x8(&two_d, narya_curve_2d);
    narya_r51x8_add_ifma(&out->Y_plus_X, &point->Y, &point->X);
    narya_r51x8_sub_ifma(&out->Y_minus_X, &point->Y, &point->X);
    memcpy(&out->Z, &point->Z, sizeof(out->Z));
    narya_r51x8_mul_ifma(&out->T2d, &point->T, &two_d);
}

void
narya_edwards_add_projective_niels_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point,
    const narya_projective_niels_x8 *cached)
{
    narya_niels_stage2_workspace_x8 stage2;

    /*
     * Projective-Niels addition, following the same operand convention used
     * by the Go r51 verifier:
     *
     *   A=(Y-X)(Yc-Xc), B=(Y+X)(Yc+Xc)
     *   C=T(2dTc), D=2ZZc
     *   E=B-A, F=D-C, G=D+C, H=B+A
     *   X'=EF, Y'=GH, T'=EH, Z'=FG.
     *
     * All point and cached coordinates are consumed before output stores, so
     * exact out==point is supported.  out must not overlap cached.
     */
    narya_r51x8_sub_ifma(&stage2.slot[0], &point->Y, &point->X);
    narya_r51x8_add_ifma(&stage2.slot[1], &point->Y, &point->X);
    narya_projective_niels_stage2_ifma(&stage2, point, cached);
    narya_r51x8_mul_ifma(&out->X, &stage2.slot[0], &stage2.slot[1]);
    narya_r51x8_mul_ifma(&out->Y, &stage2.slot[2], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->T, &stage2.slot[0], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->Z, &stage2.slot[1], &stage2.slot[2]);
}

void
narya_edwards_add_affine_niels_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point,
    const narya_affine_niels_x8 *cached)
{
    narya_niels_stage2_workspace_x8 stage2;

    /*
     * Affine-Niels specialization of the formula above. The cached point has
     * Zc=1, so D=2*Z and the fourth input multiplication disappears:
     *
     *   A=(Y-X)(Yc-Xc), B=(Y+X)(Yc+Xc), C=T(2dTc), D=2Z.
     *
     * This is seven field multiplications total including the four output
     * products. Inputs are dead before output stores, so out==point is safe.
     */
    narya_r51x8_sub_ifma(&stage2.slot[0], &point->Y, &point->X);
    narya_r51x8_add_ifma(&stage2.slot[1], &point->Y, &point->X);
    narya_affine_niels_stage2_ifma(&stage2, point, cached);
    narya_r51x8_mul_ifma(&out->X, &stage2.slot[0], &stage2.slot[1]);
    narya_r51x8_mul_ifma(&out->Y, &stage2.slot[2], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->T, &stage2.slot[0], &stage2.slot[3]);
    narya_r51x8_mul_ifma(&out->Z, &stage2.slot[1], &stage2.slot[2]);
}
