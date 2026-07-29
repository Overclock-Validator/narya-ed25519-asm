/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Coordinate-parallel singleton point layer.
 *
 * Lanes 0..3 of one r51x8 value contain [X,Y,T,Z] for one Edwards point.
 * The existing native-512 field leaf therefore computes four independent
 * coordinate products with one five-limb multiplication schedule. This is
 * the singleton analogue of the signature-parallel x8 path: lanes never mix
 * verification equations, but within this file lane permutations are an
 * explicit part of the point formula.
 *
 * The formulas and signed-integer NAF schedule mirror Narya's reviewed Go
 * packed verifier. The immutable generator table is independently generated
 * by tools/generate_packed_naf_basepoint.py from affine big-integer Edwards
 * arithmetic. Longer contracts live in
 * docs/architecture/PACKED_SINGLETON.md.
 */
#include "internal.h"

#include <stdint.h>
#include <string.h>

enum { packed_lanes = 4, packed_naf_bits = 256 };

static const uint64_t curve_2d[5] = {
    UINT64_C(1859910466990425), UINT64_C(932731440258426),
    UINT64_C(1072319116312658), UINT64_C(1815898335770999),
    UINT64_C(633789495995903),
};

static uint64_t
subtraction_bias(size_t limb)
{
    const uint64_t radix = UINT64_C(1) << 51;
    return limb == 0 ? 4 * radix - 76 : 4 * radix - 4;
}

static void
packed_identity(narya_packed_point_x4 *point)
{
    *point = (narya_packed_point_x4){0};
    point->coordinates.limb[0][1] = 1;
    point->coordinates.limb[0][3] = 1;
    point->coordinates.limb[0][5] = 1;
    point->coordinates.limb[0][7] = 1;
}

void
narya_packed_point_from_lanes_x4(
    narya_packed_point_x4 *out,
    const narya_edwards_point_x8 *point,
    const size_t lane[2],
    uint8_t active)
{
    *out = (narya_packed_point_x4){0};
    for (size_t chain = 0; chain < 2; chain++) {
        const size_t base = chain * packed_lanes;
        if ((active & (UINT8_C(1) << chain)) == 0) {
            out->coordinates.limb[0][base + 1] = 1;
            out->coordinates.limb[0][base + 3] = 1;
            continue;
        }
        for (size_t limb = 0; limb < 5; limb++) {
            out->coordinates.limb[limb][base + 0] =
                point->X.limb[limb][lane[chain]];
            out->coordinates.limb[limb][base + 1] =
                point->Y.limb[limb][lane[chain]];
            out->coordinates.limb[limb][base + 2] =
                point->T.limb[limb][lane[chain]];
            out->coordinates.limb[limb][base + 3] =
                point->Z.limb[limb][lane[chain]];
        }
    }
}

/* [X,Y,T,Z] -> normalized [Y-X,Y+X,T,Z]. */
static void
cached_first_operand(narya_r51x8 *out, const narya_packed_point_x4 *point)
{
    narya_packed_cached_first_operand_ifma(out, &point->coordinates);
}

static void
cache_point(
    narya_packed_cached_x4 *out,
    const narya_packed_point_x4 *point)
{
    narya_r51x8 coordinates, scale = {0};
    cached_first_operand(&coordinates, point);
    scale.limb[0][0] = 1;
    scale.limb[0][1] = 1;
    scale.limb[0][3] = 2;
    scale.limb[0][4] = 1;
    scale.limb[0][5] = 1;
    scale.limb[0][7] = 2;
    for (size_t limb = 0; limb < 5; limb++) {
        scale.limb[limb][2] = curve_2d[limb];
        scale.limb[limb][6] = curve_2d[limb];
    }
    narya_r51x8_mul_ifma(&out->coordinates, &coordinates, &scale);
}

/* Two packed field products implement one complete extended doubling. */
static void
packed_double(narya_packed_point_x4 *out, const narya_packed_point_x4 *point)
{
    narya_r51x8 left, right, products;
    narya_packed_double_first_operands_ifma(
        &left, &right, &point->coordinates);
    narya_r51x8_mul_ifma(&products, &left, &right);
    narya_packed_double_final_multiply_ifma(&out->coordinates, &products);
}

static void
packed_add_cached(
    narya_packed_point_x4 *out,
    const narya_packed_point_x4 *point,
    const narya_packed_cached_x4 *cached)
{
    narya_r51x8 point_operand, products;
    cached_first_operand(&point_operand, point);
    narya_r51x8_mul_ifma(&products, &point_operand, &cached->coordinates);
    narya_packed_cached_final_multiply_ifma(&out->coordinates, &products);
}

void
narya_packed_naf_table5_build_x4(
    narya_packed_naf_table5_x4 *out,
    const narya_packed_point_x4 *base)
{
    narya_packed_point_x4 current = *base;
    cache_point(&out->positive[0], &current);
    narya_packed_point_x4 twice = current;
    packed_double(&twice, &twice);
    narya_packed_cached_x4 twice_cached;
    cache_point(&twice_cached, &twice);
    for (size_t entry = 1; entry < 8; entry++) {
        packed_add_cached(&current, &current, &twice_cached);
        cache_point(&out->positive[entry], &current);
    }
}

static uint64_t
load_le64(const uint8_t input[8])
{
    uint64_t value = 0;
    for (size_t byte = 0; byte < 8; byte++)
        value |= (uint64_t)input[byte] << (8 * byte);
    return value;
}

/* Exact signed-integer width-w NAF; no reduction modulo l occurs here. */
static int
recode_naf(int8_t out[packed_naf_bits], const uint8_t scalar[32], unsigned width)
{
    memset(out, 0, packed_naf_bits);
    if (width < 2 || width > 8 || !narya_scalar_is_canonical(scalar))
        return 0;
    uint64_t words[5] = {0};
    for (size_t word = 0; word < 4; word++)
        words[word] = load_le64(&scalar[word * 8]);
    const uint64_t radix = UINT64_C(1) << width;
    const uint64_t mask = radix - 1;
    uint64_t carry = 0;
    for (unsigned position = 0; position < packed_naf_bits;) {
        const unsigned word = position >> 6;
        const unsigned bit = position & 63;
        uint64_t buffer = words[word] >> bit;
        if (bit >= 64 - width)
            buffer |= words[word + 1] << (64 - bit);
        const uint64_t window = carry + (buffer & mask);
        if ((window & 1) == 0) {
            position++;
            continue;
        }
        if (window < radix / 2) {
            carry = 0;
            out[position] = (int8_t)window;
        } else {
            carry = 1;
            out[position] = (int8_t)((int)window - (int)radix);
        }
        position += width;
    }
    return 1;
}

static void
negate_cached_half(narya_packed_cached_x4 *point, size_t chain)
{
    const size_t base = chain * packed_lanes;
    uint64_t negative[5];
    for (size_t limb = 0; limb < 5; limb++) {
        const uint64_t temporary = point->coordinates.limb[limb][base + 0];
        point->coordinates.limb[limb][base + 0] =
            point->coordinates.limb[limb][base + 1];
        point->coordinates.limb[limb][base + 1] = temporary;
        negative[limb] =
            subtraction_bias(limb) - point->coordinates.limb[limb][base + 2];
    }
    const uint64_t mask = (UINT64_C(1) << 51) - 1;
    uint64_t carry[5];
    for (size_t limb = 0; limb < 5; limb++)
        carry[limb] = negative[limb] >> 51;
    point->coordinates.limb[0][base + 2] =
        (negative[0] & mask) + 19 * carry[4];
    for (size_t limb = 1; limb < 5; limb++)
        point->coordinates.limb[limb][base + 2] =
            (negative[limb] & mask) + carry[limb - 1];
}

static void
cached_identity(narya_packed_cached_x4 *point)
{
    *point = (narya_packed_cached_x4){0};
    point->coordinates.limb[0][0] = 1;
    point->coordinates.limb[0][1] = 1;
    point->coordinates.limb[0][3] = 2;
    point->coordinates.limb[0][4] = 1;
    point->coordinates.limb[0][5] = 1;
    point->coordinates.limb[0][7] = 2;
}

static void
copy_cached_half(
    narya_packed_cached_x4 *out,
    const narya_packed_cached_x4 *source,
    size_t chain)
{
    const size_t base = chain * packed_lanes;
    for (size_t limb = 0; limb < 5; limb++)
        for (size_t coordinate = 0; coordinate < packed_lanes; coordinate++)
            out->coordinates.limb[limb][base + coordinate] =
                source->coordinates.limb[limb][base + coordinate];
}

static void
select_a(
    narya_packed_cached_x4 *out,
    const narya_packed_naf_table5_x4 *table,
    const int digit[2],
    uint8_t active)
{
    cached_identity(out);
    for (size_t chain = 0; chain < 2; chain++) {
        if ((active & (UINT8_C(1) << chain)) == 0 || digit[chain] == 0)
            continue;
        const unsigned magnitude =
            (unsigned)(digit[chain] < 0 ? -digit[chain] : digit[chain]);
        copy_cached_half(out, &table->positive[magnitude / 2], chain);
        if (digit[chain] < 0)
            negate_cached_half(out, chain);
    }
}

static void
select_b(
    narya_packed_cached_x4 *out,
    const int digit[2],
    uint8_t active)
{
    cached_identity(out);
    for (size_t chain = 0; chain < 2; chain++) {
        if ((active & (UINT8_C(1) << chain)) == 0 || digit[chain] == 0)
            continue;
        const unsigned magnitude =
            (unsigned)(digit[chain] < 0 ? -digit[chain] : digit[chain]);
        const narya_packed_naf_micro_entry_x4 *source =
            &narya_packed_naf_basepoint[magnitude / 2];
        const size_t base = chain * packed_lanes;
        for (size_t limb = 0; limb < 5; limb++)
            for (size_t coordinate = 0; coordinate < packed_lanes; coordinate++)
                out->coordinates.limb[limb][base + coordinate] =
                    source->limb[limb][coordinate];
        if (digit[chain] < 0)
            negate_cached_half(out, chain);
    }
}

int
narya_packed_double_scalar_mult_x4(
    narya_packed_point_x4 *out,
    const narya_packed_naf_table5_x4 *a_table,
    const uint8_t *s,
    const uint8_t *k,
    uint8_t active)
{
    int8_t a_naf[2][packed_naf_bits] = {{0}};
    int8_t b_naf[2][packed_naf_bits] = {{0}};
    uint8_t valid = 0;
    for (size_t chain = 0; chain < 2; chain++) {
        const uint8_t mask = (uint8_t)(UINT8_C(1) << chain);
        if ((active & mask) != 0 &&
            recode_naf(a_naf[chain], &k[chain * 32], 5) &&
            recode_naf(b_naf[chain], &s[chain * 32], 8))
            valid |= mask;
    }
    narya_packed_point_x4 accumulator;
    packed_identity(&accumulator);
    if (valid == 0) {
        *out = accumulator;
        return 0;
    }
    int high = packed_naf_bits - 1;
    while (high >= 0 && a_naf[0][high] == 0 && b_naf[0][high] == 0 &&
           a_naf[1][high] == 0 && b_naf[1][high] == 0)
        high--;
    for (int bit = high; bit >= 0; bit--) {
        packed_double(&accumulator, &accumulator);
        const int a_digit[2] = {-a_naf[0][bit], -a_naf[1][bit]};
        if (a_digit[0] != 0 || a_digit[1] != 0) {
            narya_packed_cached_x4 selected;
            select_a(&selected, a_table, a_digit, valid);
            packed_add_cached(&accumulator, &accumulator, &selected);
        }
        const int b_digit[2] = {b_naf[0][bit], b_naf[1][bit]};
        if (b_digit[0] != 0 || b_digit[1] != 0) {
            narya_packed_cached_x4 selected;
            select_b(&selected, b_digit, valid);
            packed_add_cached(&accumulator, &accumulator, &selected);
        }
    }
    *out = accumulator;
    return valid;
}

static int
canonical_lanes_equal(
    const narya_r51x8 *left,
    size_t left_lane,
    const narya_r51x8 *right,
    size_t right_lane)
{
    uint64_t a[5], b[5], difference = 0;
    narya_r51x8_canonical_lane(a, left, left_lane);
    narya_r51x8_canonical_lane(b, right, right_lane);
    for (size_t limb = 0; limb < 5; limb++)
        difference |= a[limb] ^ b[limb];
    return difference == 0;
}

uint8_t
narya_packed_equal_decoded_lanes_x4(
    const narya_packed_point_x4 *point,
    const narya_edwards_point_x8 *decoded,
    const size_t lane[2],
    uint8_t active)
{
    narya_r51x8 affine = {0}, z = {0}, cross;
    for (size_t chain = 0; chain < 2; chain++) {
        if ((active & (UINT8_C(1) << chain)) == 0)
            continue;
        const size_t base = chain * packed_lanes;
        for (size_t limb = 0; limb < 5; limb++) {
            affine.limb[limb][base + 0] = decoded->X.limb[limb][lane[chain]];
            affine.limb[limb][base + 1] = decoded->Y.limb[limb][lane[chain]];
            z.limb[limb][base + 0] = point->coordinates.limb[limb][base + 3];
            z.limb[limb][base + 1] = point->coordinates.limb[limb][base + 3];
        }
    }
    narya_r51x8_mul_ifma(&cross, &affine, &z);
    uint8_t equal = 0;
    for (size_t chain = 0; chain < 2; chain++) {
        const uint8_t mask = (uint8_t)(UINT8_C(1) << chain);
        if ((active & mask) == 0)
            continue;
        const size_t base = chain * packed_lanes;
        uint64_t canonical_z[5], z_or = 0;
        narya_r51x8_canonical_lane(
            canonical_z, &point->coordinates, base + 3);
        for (size_t limb = 0; limb < 5; limb++)
            z_or |= canonical_z[limb];
        if (z_or != 0 &&
            canonical_lanes_equal(
                &point->coordinates, base + 0, &cross, base + 0) &&
            canonical_lanes_equal(
                &point->coordinates, base + 1, &cross, base + 1))
            equal |= mask;
    }
    return equal;
}
