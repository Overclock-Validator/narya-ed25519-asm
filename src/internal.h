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
/*
 * Computes `count` dependent squares while retaining the five running limbs
 * in ZMM registers. The source must satisfy the same composable-u52 contract
 * as narya_r51x8_mul_ifma; count zero copies x to out. Exact in-place use is
 * supported.
 */
void narya_r51x8_repeated_square_ifma(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    unsigned int count);
void narya_r51x8_add_ifma(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
void narya_r51x8_sub_ifma(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
void narya_r51x8_neg_ifma(narya_r51x8 *out, const narya_r51x8 *x);

/*
 * Canonicalizes one lane from the composable u52 domain into five radix-51
 * limbs representing the unique integer in [0,p). This is the single shared
 * implementation used by decoder sign/equality decisions and final
 * projective equality; duplicating it would duplicate consensus-visible
 * reduction policy.
 */
void narya_r51x8_canonical_lane(
    uint64_t output[5],
    const narya_r51x8 *input,
    size_t lane);

void narya_sha512_compress_x8_asm(
    narya_sha512_state_x8 *state,
    const narya_sha512_block_x8 *block);

/*
 * In-place signed radix-2^21 reducer. limbs[index][lane] contains 24 limbs
 * produced by scalar_reduce.c. The assembly leaf leaves canonical limbs
 * 0..11 in place. See docs/proofs/SCALAR_REDUCTION_CONTRACT.md.
 */
void narya_scalar_reduce_radix21_x8_asm(int64_t limbs[24][8]);

enum {
    NARYA_RADIX32_BITS = 5,
    NARYA_RADIX32_ROUNDS = 51,
    NARYA_RADIX32_ENTRIES = 16
};

/*
 * Round-major balanced radix-32 digits for eight independent scalars.
 * magnitude is in [0,16]. The masks duplicate digit sign/zero state so the
 * eventual constant-shape table selector never branches on secret material
 * (verification scalars are public, but one representation serves all paths).
 */
typedef struct narya_radix32_round_x8 {
    uint8_t magnitude[8];
    uint8_t nonzero_mask;
    uint8_t negative_mask;
} narya_radix32_round_x8;

typedef struct narya_radix32_digits_x8 {
    narya_radix32_round_x8 round[NARYA_RADIX32_ROUNDS];
    uint8_t valid_mask;
} narya_radix32_digits_x8;

/* Exact-integer recoding: negative_mask negates digits, not scalars modulo l. */
uint8_t narya_scalar_recode_radix32_x8(
    narya_radix32_digits_x8 *out,
    const uint8_t scalar[8 * 32],
    uint8_t negative_mask,
    uint8_t active);

/* One key's contiguous [Y+X,Y-X,Z,2dT] row for one positive magnitude. */
typedef struct narya_projective_niels_micro_entry_x8 {
    uint64_t limb[5][4];
} narya_projective_niels_micro_entry_x8;

_Static_assert(
    sizeof(narya_projective_niels_micro_entry_x8) == 160,
    "projective transpose source ABI changed");

/*
 * The cold table stores positive and negative entries explicitly. Public
 * scalar signs can therefore select an already-signed point without a second
 * field negation in every radix round. Layout is key, sign, magnitude.
 */
typedef struct narya_projective_niels_presigned_table_x8 {
    narya_projective_niels_micro_entry_x8 point[8][2][16];
} narya_projective_niels_presigned_table_x8;

/* Extended Edwards coordinates, internal until the complete verifier ABI. */
typedef struct narya_edwards_point_x8 {
    narya_r51x8 X;
    narya_r51x8 Y;
    narya_r51x8 Z;
    narya_r51x8 T;
} narya_edwards_point_x8;

/*
 * Projective P2 coordinates for a run of dependent doublings.  This is a
 * distinct type, rather than an Edwards point with a stale T coordinate:
 * additions require narya_edwards_point_x8 and therefore cannot consume an
 * intermediate whose T was deliberately omitted.  See the cold-path parity
 * note in docs/architecture/PORTING_PLAN.md.
 */
typedef struct narya_projective_point_x8 {
    narya_r51x8 X;
    narya_r51x8 Y;
    narya_r51x8 Z;
} narya_projective_point_x8;

/*
 * Private state transition for doubling. On entry the assembly leaf derives
 * exact folded raw products [X^2,Y^2,Z^2,XY] from three composable-u52
 * coordinates. On return these slots hold normalized [E,F,G,H], where
 *
 *   E=2XY, G=Y^2-X^2, F=G-2Z^2, H=-X^2-Y^2 (mod p).
 *
 * The distinct type prevents raw u61 products from being mistaken for legal
 * IFMA sources. The output never overlaps any input coordinate.
 */
typedef struct narya_double_stage2_workspace_x8 {
    narya_r51x8 slot[4];
} narya_double_stage2_workspace_x8;

void narya_r51x8_double_stage2_ifma(
    narya_double_stage2_workspace_x8 *workspace,
    const narya_r51x8 *X,
    const narya_r51x8 *Y,
    const narya_r51x8 *Z);

/* Cached projective-Niels form (Y+X, Y-X, Z, 2dT). */
typedef struct narya_projective_niels_x8 {
    narya_r51x8 Y_plus_X;
    narya_r51x8 Y_minus_X;
    narya_r51x8 Z;
    narya_r51x8 T2d;
} narya_projective_niels_x8;

_Static_assert(sizeof(narya_r51x8) == 320, "r51x8 assembly ABI changed");
_Static_assert(
    offsetof(narya_projective_niels_x8, Y_minus_X) == 320 &&
        offsetof(narya_projective_niels_x8, Z) == 640 &&
        offsetof(narya_projective_niels_x8, T2d) == 960 &&
        sizeof(narya_projective_niels_x8) == 1280,
    "projective transpose destination ABI changed");

/* Dense scalar affine-Niels entry and arithmetic SoA selection. */
typedef struct narya_affine_niels_micro_entry_x8 {
    uint64_t limb[5][3];
} narya_affine_niels_micro_entry_x8;

_Static_assert(
    sizeof(narya_affine_niels_micro_entry_x8) == 120,
    "affine transpose source ABI changed");

typedef struct narya_affine_niels_x8 {
    narya_r51x8 Y_plus_X;
    narya_r51x8 Y_minus_X;
    narya_r51x8 T2d;
} narya_affine_niels_x8;

_Static_assert(
    offsetof(narya_affine_niels_x8, Y_minus_X) == 320 &&
        offsetof(narya_affine_niels_x8, T2d) == 640 &&
        sizeof(narya_affine_niels_x8) == 960,
    "affine transpose destination ABI changed");

extern const narya_affine_niels_micro_entry_x8
    narya_fixed_base_comb_r256[16][128][2];
void narya_affine_niels_transpose_x8_asm(
    narya_affine_niels_x8 *out,
    const narya_affine_niels_micro_entry_x8 *const source[8]);
uint8_t narya_fixed_base_scalar_mult_x8(
    narya_edwards_point_x8 *out,
    const uint8_t scalar[8 * 32],
    uint8_t active);

void narya_projective_niels_transpose_x8_asm(
    narya_projective_niels_x8 *out,
    const narya_projective_niels_micro_entry_x8 *const source[8]);
void narya_projective_niels_table_build_x8(
    narya_projective_niels_presigned_table_x8 *out,
    const narya_edwards_point_x8 *base);
void narya_projective_niels_table_select_x8(
    narya_projective_niels_x8 *out,
    const narya_projective_niels_presigned_table_x8 *table,
    const narya_radix32_round_x8 *round,
    uint8_t active);
uint8_t narya_variable_scalar_mult_x8(
    narya_edwards_point_x8 *out,
    const narya_projective_niels_presigned_table_x8 *table,
    const uint8_t scalar[8 * 32],
    uint8_t negative_mask,
    uint8_t active);

/* Unchecked: caller proves CPU support, u52 limbs, and a valid point. */
void narya_edwards_double_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point);
void narya_edwards_double_to_projective_x8(
    narya_projective_point_x8 *out,
    const narya_edwards_point_x8 *point);
void narya_projective_double_x8(
    narya_projective_point_x8 *out,
    const narya_projective_point_x8 *point);
void narya_projective_double_to_edwards_x8(
    narya_edwards_point_x8 *out,
    const narya_projective_point_x8 *point);
void narya_edwards_to_projective_niels_x8(
    narya_projective_niels_x8 *out,
    const narya_edwards_point_x8 *point);
void narya_edwards_add_projective_niels_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point,
    const narya_projective_niels_x8 *cached);
void narya_edwards_add_affine_niels_x8(
    narya_edwards_point_x8 *out,
    const narya_edwards_point_x8 *point,
    const narya_affine_niels_x8 *cached);

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
