/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#ifndef NARYA_ED25519_ASM_INTERNAL_H
#define NARYA_ED25519_ASM_INTERNAL_H

#include "narya_ed25519_asm.h"

/*
 * Internal unchecked leaf.  It assumes both the CPU feature gate and the u52
 * source bounds have already been established.  Keeping this symbol out of
 * the public header makes the checked C wrapper the supported ABI while point
 * kernels may call the leaf directly once their range certificate proves the
 * same preconditions.
 */
void narya_r51x8_mul_ifma(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
void narya_r51x8_add_ifma(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
void narya_r51x8_sub_ifma(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
void narya_r51x8_neg_ifma(narya_r51x8 *out, const narya_r51x8 *x);

/* Extended Edwards coordinates, internal until the complete verifier ABI. */
typedef struct narya_edwards_point_x8 {
    narya_r51x8 X;
    narya_r51x8 Y;
    narya_r51x8 Z;
    narya_r51x8 T;
} narya_edwards_point_x8;

/* Unchecked: caller proves CPU support, u52 limbs, and a valid point. */
void narya_edwards_double_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point);

#endif
