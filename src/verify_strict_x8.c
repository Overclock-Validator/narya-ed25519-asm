/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Complete, audit-first DalekStrict verifier assembled from the independently
 * gated x8 components. The cold equation merges the immutable width-10
 * generator table into the variable-base radix-32 doubling chain. The
 * independent radix-256 comb remains a differential oracle.
 *
 * Predicate and proof map:
 *   docs/architecture/STRICT_PREDICATE.md
 *   docs/architecture/VARIABLE_SCALAR_MULTIPLICATION.md
 *   docs/proofs/FORMALIZATION_BACKLOG.md
 */
#include "internal.h"

#include <stdalign.h>
#include <stdint.h>
#include <string.h>

typedef union narya_verify_strict_workspace_x8 {
    narya_projective_niels_presigned_table_x8 public_table;
    narya_packed_naf_table5_x4 packed_public_table;
} narya_verify_strict_workspace_x8;

enum { strict_batch_groups = NARYA_VERIFY_STRICT_BATCH_MAX / NARYA_X8_LANES };

typedef struct narya_verify_strict_batch_workspace {
    narya_verify_strict_workspace_x8 group;
    narya_edwards_point_x8 equation[strict_batch_groups];
    narya_r51x8 prefix[strict_batch_groups];
    narya_r51x8 inverse_z[strict_batch_groups];
    uint8_t live[strict_batch_groups];
} narya_verify_strict_batch_workspace;

typedef union narya_digest_batch_x8 {
    uint8_t lane[8][64];
    uint8_t flat[8 * 64];
} narya_digest_batch_x8;

typedef union narya_scalar_batch_x8 {
    uint8_t lane[8][32];
    uint8_t flat[8 * 32];
} narya_scalar_batch_x8;

static const uint8_t scalar_order[32] = {
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
};

static const uint8_t small_order_alpha[32] = {
    0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f,
    0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67, 0x0f,
    0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6,
    0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac, 0x03, 0x7a,
};

static const uint8_t small_order_neg_alpha[32] = {
    0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0,
    0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98, 0xf0,
    0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39,
    0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53, 0xfc, 0x05,
};

static int
bytes_less_than(const uint8_t value[32], const uint8_t limit[32])
{
    for (size_t index = 32; index-- > 0;) {
        if (value[index] != limit[index])
            return value[index] < limit[index];
    }
    return 0;
}

static int
low255_tail_equal(const uint8_t value[32], uint8_t middle, uint8_t last)
{
    uint8_t difference = (value[31] & 0x7fU) ^ last;
    for (size_t index = 1; index < 31; index++)
        difference |= value[index] ^ middle;
    return difference == 0;
}

static int
low255_equal(const uint8_t value[32], const uint8_t expected[32])
{
    uint8_t difference = (value[31] & 0x7fU) ^ expected[31];
    for (size_t index = 0; index < 31; index++)
        difference |= value[index] ^ expected[index];
    return difference == 0;
}

/* Exact classifier for all 14 encodings of the eight pure-torsion points. */
static int
small_order_encoding(const uint8_t value[32])
{
    switch (value[0]) {
    case 0x00:
    case 0x01:
        return low255_tail_equal(value, 0x00, 0x00);
    case 0x26:
        return low255_equal(value, small_order_neg_alpha);
    case 0xc7:
        return low255_equal(value, small_order_alpha);
    case 0xec:
    case 0xed:
    case 0xee:
        return low255_tail_equal(value, 0xff, 0x7f);
    default:
        return 0;
    }
}

static int
low255_less_than_p(const uint8_t value[32])
{
    if ((value[31] & 0x7fU) != 0x7fU)
        return 1;
    for (size_t index = 31; index-- > 1;)
        if (value[index] != 0xffU)
            return 1;
    return value[0] < 0xedU;
}

/* Canonicality is independent of the small-order gate by construction. */
static int
canonical_r_encoding(const uint8_t value[32])
{
    if (!low255_less_than_p(value))
        return 0;
    if ((value[31] & 0x80U) == 0)
        return 1;
    if (value[0] == 0x01U && low255_tail_equal(value, 0x00, 0x00))
        return 0;
    if (value[0] == 0xecU && low255_tail_equal(value, 0xff, 0x7f))
        return 0;
    return 1;
}

static uint8_t
byte_precheck(
    const uint8_t public_key[8 * 32],
    const uint8_t signature[8 * 64],
    uint8_t active)
{
    uint8_t live = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        const uint8_t lane_mask = (uint8_t)(UINT8_C(1) << lane);
        const uint8_t *a = &public_key[lane * 32];
        const uint8_t *r = &signature[lane * 64];
        const uint8_t *s = &signature[lane * 64 + 32];
        if ((active & lane_mask) != 0 &&
            bytes_less_than(s, scalar_order) &&
            !small_order_encoding(a) &&
            !small_order_encoding(r) &&
            canonical_r_encoding(r))
            live |= lane_mask;
    }
    return live;
}

static int
byte_precheck_one(
    const uint8_t public_key[32],
    const uint8_t signature[64])
{
    const uint8_t *r = signature;
    const uint8_t *s = signature + 32;
    return bytes_less_than(s, scalar_order) &&
           !small_order_encoding(public_key) &&
           !small_order_encoding(r) && canonical_r_encoding(r);
}

static uint8_t
field_equal_mask(const narya_r51x8 *a, const narya_r51x8 *b)
{
    uint8_t equal = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        uint64_t left[5], right[5], difference = 0;
        narya_r51x8_canonical_lane(left, a, lane);
        narya_r51x8_canonical_lane(right, b, lane);
        for (size_t limb = 0; limb < 5; limb++)
            difference |= left[limb] ^ right[limb];
        if (difference == 0)
            equal |= (uint8_t)(UINT8_C(1) << lane);
    }
    return equal;
}

/*
 * Equality of valid extended points without inversion or serialization.
 * field_equal_mask canonicalizes before comparison: comparing redundant r51
 * limb vectors directly would be wrong. Decoder and point-operation contracts
 * establish nonzero projective Z for every live lane. See
 * docs/architecture/STRICT_PREDICATE.md.
 */
static uint8_t
point_equal_mask(
    const narya_edwards_point_x8 *a,
    const narya_edwards_point_x8 *b)
{
    narya_r51x8 axbz, bxaz, aybz, byaz;
    narya_r51x8_mul_ifma(&axbz, &a->X, &b->Z);
    narya_r51x8_mul_ifma(&bxaz, &b->X, &a->Z);
    narya_r51x8_mul_ifma(&aybz, &a->Y, &b->Z);
    narya_r51x8_mul_ifma(&byaz, &b->Y, &a->Z);
    return field_equal_mask(&axbz, &bxaz) & field_equal_mask(&aybz, &byaz);
}

/*
 * Prepare one independent x8 equation without decoding R. The batch
 * finalizer later encodes all prepared Q points with one cross-group inverse.
 * Inputs always name eight readable rows; the public batch wrapper pads its
 * only possible partial tail before entering here.
 */
static narya_status
prepare_batch_equation(
    narya_edwards_point_x8 *equation,
    uint8_t *prepared_mask,
    const uint8_t public_key[8 * 32],
    const uint8_t signature[8 * 64],
    const uint8_t *const message[8],
    const size_t message_length[8],
    uint8_t active,
    narya_verify_strict_workspace_x8 *scratch)
{
    uint8_t live = byte_precheck(public_key, signature, active);
    *equation = (narya_edwards_point_x8){0};
    *prepared_mask = 0;
    if (live == 0)
        return NARYA_OK;

    uint8_t r_bytes[8 * 32], s_bytes[8 * 32];
    for (size_t lane = 0; lane < 8; lane++) {
        memcpy(&r_bytes[lane * 32], &signature[lane * 64], 32);
        memcpy(&s_bytes[lane * 32], &signature[lane * 64 + 32], 32);
    }

    narya_digest_batch_x8 digest;
    narya_scalar_batch_x8 challenge;
    narya_status status = narya_sha512_r_a_message_x8(
        digest.lane, r_bytes, public_key, message, message_length, live);
    if (status != NARYA_OK)
        return status;
    status = narya_scalar_reduce_x8(challenge.lane, digest.flat, live);
    if (status != NARYA_OK)
        return status;

    narya_edwards_point_x8 public_point;
    live &= narya_edwards_decode_x8(&public_point, public_key, live);
    if (live == 0)
        return NARYA_OK;

    narya_projective_niels_table_build_x8(
        &scratch->public_table, &public_point);
    live &= narya_asymmetric_fixed_b10_double_scalar_mult_x8(
        equation, &scratch->public_table, s_bytes, challenge.flat, live);
    *prepared_mask = live;
    return NARYA_OK;
}

/*
 * Exact coordinate-parallel singleton verifier. A and R share one x8 decode
 * schedule in lanes 0 and 1; the equation then moves to packed [X,Y,T,Z]
 * lanes and uses the width-5/width-8 signed NAF schedule. The final comparison
 * is projective and therefore performs no inversion or serialization.
 */
static narya_status
verify_packed_small(
    uint8_t *verdict,
    const uint8_t *public_key,
    const uint8_t *signature,
    const uint8_t *const *message,
    const size_t *message_length,
    size_t count,
    narya_verify_strict_workspace_x8 *scratch)
{
    *verdict = 0;
    uint8_t live = 0;
    for (size_t item = 0; item < count; item++)
        if (byte_precheck_one(
                &public_key[item * 32], &signature[item * 64]))
            live |= (uint8_t)(UINT8_C(1) << item);
    if (live == 0)
        return NARYA_OK;

    uint8_t r_bytes[8 * 32] = {0};
    uint8_t a_bytes[8 * 32] = {0};
    const uint8_t *messages[8] = {0};
    size_t lengths[8] = {0};
    for (size_t item = 0; item < count; item++) {
        memcpy(&r_bytes[item * 32], &signature[item * 64], 32);
        memcpy(&a_bytes[item * 32], &public_key[item * 32], 32);
        messages[item] = message[item];
        lengths[item] = message_length[item];
    }
    narya_digest_batch_x8 digest;
    narya_scalar_batch_x8 challenge;
    narya_status status = narya_sha512_r_a_message_x8(
        digest.lane, r_bytes, a_bytes, messages, lengths, live);
    if (status != NARYA_OK)
        return status;
    status = narya_scalar_reduce_x8(
        challenge.lane, digest.flat, live);
    if (status != NARYA_OK)
        return status;

    /* Decode each (A,R) pair together in adjacent lanes. */
    uint8_t encoded[8 * 32] = {0};
    uint8_t decode_active = 0;
    for (size_t item = 0; item < count; item++) {
        if ((live & (UINT8_C(1) << item)) == 0)
            continue;
        memcpy(&encoded[(2 * item) * 32], &public_key[item * 32], 32);
        memcpy(&encoded[(2 * item + 1) * 32], &signature[item * 64], 32);
        decode_active |= (uint8_t)(UINT8_C(3) << (2 * item));
    }
    narya_edwards_point_x8 decoded;
    const uint8_t decoded_mask =
        narya_edwards_decode_x8(&decoded, encoded, decode_active);
    for (size_t item = 0; item < count; item++) {
        const uint8_t pair = (uint8_t)(UINT8_C(3) << (2 * item));
        if ((decoded_mask & pair) != pair)
            live &= (uint8_t)~(UINT8_C(1) << item);
    }
    if (live == 0)
        return NARYA_OK;

    narya_packed_point_x4 public_point;
    const size_t public_lane[2] = {0, 2};
    narya_packed_point_from_lanes_x4(
        &public_point, &decoded, public_lane, live);
    narya_packed_naf_table5_build_x4(
        &scratch->packed_public_table, &public_point);

    uint8_t s[2][32] = {{0}}, k[2][32] = {{0}};
    for (size_t item = 0; item < count; item++) {
        memcpy(s[item], &signature[item * 64 + 32], 32);
        memcpy(k[item], challenge.lane[item], 32);
    }
    narya_packed_point_x4 equation;
    live &= (uint8_t)narya_packed_double_scalar_mult_x4(
        &equation, &scratch->packed_public_table, &s[0][0], &k[0][0], live);
    if (live == 0)
        return NARYA_OK;
    const size_t r_lane[2] = {1, 3};
    *verdict = narya_packed_equal_decoded_lanes_x4(
        &equation, &decoded, r_lane, live) & live;
    return NARYA_OK;
}

static uint8_t
field_zero_mask(const narya_r51x8 *value)
{
    uint8_t zero = 0;
    for (size_t lane = 0; lane < 8; lane++) {
        uint64_t canonical[5], combined = 0;
        narya_r51x8_canonical_lane(canonical, value, lane);
        for (size_t limb = 0; limb < 5; limb++)
            combined |= canonical[limb];
        if (combined == 0)
            zero |= (uint8_t)(UINT8_C(1) << lane);
    }
    return zero;
}

static void
sanitized_z(
    narya_r51x8 *out,
    const narya_edwards_point_x8 *point,
    uint8_t active)
{
    *out = point->Z;
    for (size_t lane = 0; lane < 8; lane++) {
        if ((active & (UINT8_C(1) << lane)) != 0)
            continue;
        for (size_t limb = 0; limb < 5; limb++)
            out->limb[limb][lane] = 0;
        out->limb[0][lane] = 1;
    }
}

static void
store64_le(uint8_t out[8], uint64_t value)
{
    for (size_t byte = 0; byte < 8; byte++)
        out[byte] = (uint8_t)(value >> (8 * byte));
}

static int
encoded_point_matches_lane(
    const narya_r51x8 *affine_x,
    const narya_r51x8 *affine_y,
    size_t lane,
    const uint8_t expected[32])
{
    uint64_t x[5], y[5];
    narya_r51x8_canonical_lane(x, affine_x, lane);
    narya_r51x8_canonical_lane(y, affine_y, lane);

    uint8_t encoded[32];
    store64_le(&encoded[0], y[0] | (y[1] << 51));
    store64_le(&encoded[8], (y[1] >> 13) | (y[2] << 38));
    store64_le(&encoded[16], (y[2] >> 26) | (y[3] << 25));
    store64_le(&encoded[24], (y[3] >> 39) | (y[4] << 12));
    encoded[31] |= (uint8_t)(x[0] & 1U) << 7;
    return memcmp(encoded, expected, sizeof(encoded)) == 0;
}

/*
 * Montgomery batch inversion across up to eight x8 groups. Every vector lane
 * is an independent prefix chain; no signature data crosses lanes. Inactive
 * denominators are one. A zero active denominator indicates a violated point
 * invariant and becomes a visible internal error before inversion.
 */
static narya_status
finalize_batch_equations(
    uint64_t *verdict,
    narya_verify_strict_batch_workspace *scratch,
    const uint8_t *signature,
    size_t groups)
{
    uint8_t active_lanes = 0;
    for (size_t group = 0; group < groups; group++)
        active_lanes |= scratch->live[group];
    if (active_lanes == 0) {
        *verdict = 0;
        return NARYA_OK;
    }

    narya_r51x8 z;
    sanitized_z(&z, &scratch->equation[0], scratch->live[0]);
    scratch->prefix[0] = z;
    for (size_t group = 1; group < groups; group++) {
        sanitized_z(&z, &scratch->equation[group], scratch->live[group]);
        narya_r51x8_mul_ifma(
            &scratch->prefix[group], &scratch->prefix[group - 1], &z);
    }
    if ((field_zero_mask(&scratch->prefix[groups - 1]) & active_lanes) != 0)
        return NARYA_ERR_INTERNAL;

    narya_r51x8 inverse_product;
    narya_r51x8_invert_x8(
        &inverse_product, &scratch->prefix[groups - 1]);
    for (size_t group = groups - 1; group > 0; group--) {
        narya_r51x8_mul_ifma(
            &scratch->inverse_z[group], &inverse_product,
            &scratch->prefix[group - 1]);
        sanitized_z(&z, &scratch->equation[group], scratch->live[group]);
        narya_r51x8_mul_ifma(&inverse_product, &inverse_product, &z);
    }
    scratch->inverse_z[0] = inverse_product;

    uint64_t staged = 0;
    for (size_t group = 0; group < groups; group++) {
        const uint8_t live = scratch->live[group];
        if (live == 0)
            continue;
        narya_r51x8 affine_x, affine_y;
        narya_r51x8_mul_ifma(
            &affine_x, &scratch->equation[group].X,
            &scratch->inverse_z[group]);
        narya_r51x8_mul_ifma(
            &affine_y, &scratch->equation[group].Y,
            &scratch->inverse_z[group]);
        for (size_t lane = 0; lane < 8; lane++) {
            const uint8_t lane_mask = (uint8_t)(UINT8_C(1) << lane);
            if ((live & lane_mask) != 0 &&
                encoded_point_matches_lane(
                    &affine_x, &affine_y, lane,
                    &signature[(group * 8 + lane) * 64]))
                staged |= UINT64_C(1) << (group * 8 + lane);
        }
    }
    *verdict = staged;
    return NARYA_OK;
}

size_t
narya_ed25519_verify_strict_x8_workspace_size(void)
{
    return sizeof(narya_verify_strict_workspace_x8);
}

size_t
narya_ed25519_verify_strict_x8_workspace_alignment(void)
{
    return alignof(narya_verify_strict_workspace_x8);
}

size_t
narya_ed25519_verify_strict_batch_workspace_size(void)
{
    return sizeof(narya_verify_strict_batch_workspace);
}

size_t
narya_ed25519_verify_strict_batch_workspace_alignment(void)
{
    return alignof(narya_verify_strict_batch_workspace);
}

narya_status
narya_ed25519_verify_strict_x8(
    uint8_t *verdict_mask,
    const uint8_t public_key[8 * 32],
    const uint8_t signature[8 * 64],
    const uint8_t *const message[8],
    const size_t message_length[8],
    uint8_t active,
    void *workspace,
    size_t workspace_size)
{
    if (verdict_mask == NULL || public_key == NULL || signature == NULL ||
        message == NULL || message_length == NULL || workspace == NULL ||
        workspace_size < sizeof(narya_verify_strict_workspace_x8) ||
        (uintptr_t)workspace % alignof(narya_verify_strict_workspace_x8) != 0)
        return NARYA_ERR_INVALID_ARGUMENT;
    for (size_t lane = 0; lane < 8; lane++)
        if ((active & (UINT8_C(1) << lane)) != 0 &&
            message[lane] == NULL && message_length[lane] != 0)
            return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;

    uint8_t live = byte_precheck(public_key, signature, active);
    if (live == 0) {
        *verdict_mask = 0;
        return NARYA_OK;
    }

    uint8_t r_bytes[8 * 32], s_bytes[8 * 32];
    for (size_t lane = 0; lane < 8; lane++) {
        memcpy(&r_bytes[lane * 32], &signature[lane * 64], 32);
        memcpy(&s_bytes[lane * 32], &signature[lane * 64 + 32], 32);
    }

    narya_digest_batch_x8 digest;
    narya_scalar_batch_x8 challenge;
    narya_status status = narya_sha512_r_a_message_x8(
        digest.lane, r_bytes, public_key, message, message_length, live);
    if (status != NARYA_OK)
        return status;
    status = narya_scalar_reduce_x8(challenge.lane, digest.flat, live);
    if (status != NARYA_OK)
        return status;

    narya_edwards_point_x8 public_point, r_point;
    live &= narya_edwards_decode_x8(&public_point, public_key, live);
    live &= narya_edwards_decode_x8(&r_point, r_bytes, live);
    if (live == 0) {
        *verdict_mask = 0;
        return NARYA_OK;
    }

    narya_verify_strict_workspace_x8 *scratch = workspace;
    narya_projective_niels_table_build_x8(&scratch->public_table, &public_point);

    narya_edwards_point_x8 equation;
    live &= narya_asymmetric_fixed_b10_double_scalar_mult_x8(
        &equation, &scratch->public_table, s_bytes, challenge.flat, live);
    *verdict_mask = point_equal_mask(&equation, &r_point) & live;
    return NARYA_OK;
}

narya_status
narya_ed25519_verify_strict_batch(
    uint64_t *verdict_bits,
    const uint8_t *public_key,
    const uint8_t *signature,
    const uint8_t *const *message,
    const size_t *message_length,
    size_t count,
    void *workspace,
    size_t workspace_size)
{
    if (verdict_bits == NULL || public_key == NULL || signature == NULL ||
        message == NULL || message_length == NULL || workspace == NULL ||
        count == 0 || count > NARYA_VERIFY_STRICT_BATCH_MAX ||
        workspace_size < sizeof(narya_verify_strict_batch_workspace) ||
        (uintptr_t)workspace % alignof(narya_verify_strict_batch_workspace) != 0)
        return NARYA_ERR_INVALID_ARGUMENT;
    for (size_t item = 0; item < count; item++)
        if (message[item] == NULL && message_length[item] != 0)
            return NARYA_ERR_INVALID_ARGUMENT;
    if (!narya_r51x8_available())
        return NARYA_ERR_UNSUPPORTED_CPU;

    narya_verify_strict_batch_workspace *scratch = workspace;

    /*
     * One or two signatures cannot fill the signature-parallel x8 equation.
     * Verify them through the coordinate-parallel path instead. Every verdict
     * is staged locally so an error on a later item preserves output atomicity.
     */
    if (count <= 2) {
        uint8_t staged = 0;
        const narya_status status = verify_packed_small(
            &staged, public_key, signature, message, message_length, count,
            &scratch->group);
        if (status != NARYA_OK)
            return status;
        *verdict_bits = staged;
        return NARYA_OK;
    }

    /*
     * One group is faster through the established decode-R/projective-compare
     * path: a single batch inversion has nothing to amortize there. Preserve
     * that path exactly, including partial-lane padding, and reserve the
     * cross-group encoder below for the widths that can pay for it.
     */
    if (count <= NARYA_X8_LANES) {
        if (count == NARYA_X8_LANES) {
            uint8_t staged = 0;
            const narya_status status = narya_ed25519_verify_strict_x8(
                &staged, public_key, signature, message, message_length,
                UINT8_C(0xff), &scratch->group, sizeof(scratch->group));
            if (status != NARYA_OK)
                return status;
            *verdict_bits = staged;
            return NARYA_OK;
        }
        uint8_t padded_public[8 * 32] = {0};
        uint8_t padded_signature[8 * 64] = {0};
        const uint8_t *padded_message[8] = {0};
        size_t padded_length[8] = {0};
        memcpy(padded_public, public_key, count * 32);
        memcpy(padded_signature, signature, count * 64);
        for (size_t lane = 0; lane < count; lane++) {
            padded_message[lane] = message[lane];
            padded_length[lane] = message_length[lane];
        }
        const uint8_t active =
            (uint8_t)((UINT16_C(1) << count) - 1U);
        uint8_t staged = 0;
        const narya_status status = narya_ed25519_verify_strict_x8(
            &staged, padded_public, padded_signature, padded_message,
            padded_length, active, &scratch->group, sizeof(scratch->group));
        if (status != NARYA_OK)
            return status;
        *verdict_bits = staged;
        return NARYA_OK;
    }

    const size_t groups = (count + 7) / 8;
    for (size_t group = 0; group < groups; group++) {
        const size_t offset = group * 8;
        const size_t remaining = count - offset;
        const size_t lanes = remaining < 8 ? remaining : 8;
        const uint8_t active = lanes == 8
            ? UINT8_C(0xff)
            : (uint8_t)((UINT16_C(1) << lanes) - 1U);

        const uint8_t *group_public = &public_key[offset * 32];
        const uint8_t *group_signature = &signature[offset * 64];
        const uint8_t *const *group_message = &message[offset];
        const size_t *group_length = &message_length[offset];

        uint8_t padded_public[8 * 32] = {0};
        uint8_t padded_signature[8 * 64] = {0};
        const uint8_t *padded_message[8] = {0};
        size_t padded_length[8] = {0};
        if (lanes != 8) {
            memcpy(padded_public, group_public, lanes * 32);
            memcpy(padded_signature, group_signature, lanes * 64);
            for (size_t lane = 0; lane < lanes; lane++) {
                padded_message[lane] = group_message[lane];
                padded_length[lane] = group_length[lane];
            }
            group_public = padded_public;
            group_signature = padded_signature;
            group_message = padded_message;
            group_length = padded_length;
        }

        narya_status status = prepare_batch_equation(
            &scratch->equation[group], &scratch->live[group], group_public,
            group_signature, group_message, group_length, active,
            &scratch->group);
        if (status != NARYA_OK)
            return status;
    }

    uint64_t staged = 0;
    const narya_status status = finalize_batch_equations(
        &staged, scratch, signature, groups);
    if (status != NARYA_OK)
        return status;
    *verdict_bits = staged;
    return NARYA_OK;
}
