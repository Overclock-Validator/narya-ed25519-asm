/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Audit-oriented C schedule over native field leaves.  The completed library
 * will fuse the hot linear layers in assembly, but keeping this first point
 * schedule explicit provides an independently inspectable formula boundary.
 * See docs/architecture/PORTING_PLAN.md and docs/proofs/R51_FIELD_CONTRACT.md.
 */
#include "internal.h"

void
narya_edwards_double_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point)
{
    narya_r51x8 A;
    narya_r51x8 B;
    narya_r51x8 C;
    narya_r51x8 D;
    narya_r51x8 E;
    narya_r51x8 F;
    narya_r51x8 G;
    narya_r51x8 H;

    /*
     * Complete extended-coordinate doubling for a=-1, using direct E=2XY:
     *
     *   A=X², B=Y², C=2Z², D=-A, E=2XY
     *   G=D+B, F=G-C, H=D-B
     *   X'=EF, Y'=GH, T'=EH, Z'=FG.
     *
     * Direct XY avoids the (X+Y)²-A-B identity and its extra carry boundary.
     * Every native leaf returns a composable u52 value, so the next leaf's
     * machine-range precondition is local and explicit.
     */
    narya_r51x8_mul_ifma(&A, &point->X, &point->X);
    narya_r51x8_mul_ifma(&B, &point->Y, &point->Y);
    narya_r51x8_mul_ifma(&C, &point->Z, &point->Z);
    narya_r51x8_add_ifma(&C, &C, &C);
    narya_r51x8_mul_ifma(&E, &point->X, &point->Y);
    narya_r51x8_add_ifma(&E, &E, &E);
    narya_r51x8_neg_ifma(&D, &A);
    narya_r51x8_add_ifma(&G, &D, &B);
    narya_r51x8_sub_ifma(&F, &G, &C);
    narya_r51x8_sub_ifma(&H, &D, &B);

    /* All input coordinates are dead here, so exact out==point is safe. */
    narya_r51x8_mul_ifma(&out->X, &E, &F);
    narya_r51x8_mul_ifma(&out->Y, &G, &H);
    narya_r51x8_mul_ifma(&out->T, &E, &H);
    narya_r51x8_mul_ifma(&out->Z, &F, &G);
}
