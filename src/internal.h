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

void narya_sha512_compress_x8_asm(
    narya_sha512_state_x8 *state,
    const narya_sha512_block_x8 *block);

/*
 * In-place signed radix-2^21 reducer. limbs[index][lane] contains 24 limbs
 * produced by scalar_reduce.c. The assembly leaf leaves canonical limbs
 * 0..11 in place. See docs/proofs/SCALAR_REDUCTION_CONTRACT.md.
 */
void narya_scalar_reduce_radix21_x8_asm(int64_t limbs[24][8]);

/* Extended Edwards coordinates, internal until the complete verifier ABI. */
typedef struct narya_edwards_point_x8 {
    narya_r51x8 X;
    narya_r51x8 Y;
    narya_r51x8 Z;
    narya_r51x8 T;
} narya_edwards_point_x8;

/* Cached projective-Niels form (Y+X, Y-X, Z, 2dT). */
typedef struct narya_projective_niels_x8 {
    narya_r51x8 Y_plus_X;
    narya_r51x8 Y_minus_X;
    narya_r51x8 Z;
    narya_r51x8 T2d;
} narya_projective_niels_x8;

/* Unchecked: caller proves CPU support, u52 limbs, and a valid point. */
void narya_edwards_double_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point);
void narya_edwards_to_projective_niels_x8(
    narya_projective_niels_x8 *out,
    const narya_edwards_point_x8 *point);
void narya_edwards_add_projective_niels_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point,
    const narya_projective_niels_x8 *cached);

/*
 * Permissive compressed-point decode used by the strict verifier.  Encoded y
 * is reduced modulo p and x=0 accepts either sign bit.  Invalid and inactive
 * lanes become the identity; the returned mask is a subset of `active`.
 */
uint8_t narya_edwards_decode_x8(
    narya_edwards_point_x8 *out,
    const uint8_t encoded[8 * 32],
    uint8_t active);

#endif
