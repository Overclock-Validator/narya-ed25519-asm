/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Stable C ABI for the standalone Narya Ed25519 assembly library.
 */
#ifndef NARYA_ED25519_ASM_H
#define NARYA_ED25519_ASM_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Version zero means the ABI is intentionally unstable before the verifier. */
#define NARYA_ED25519_ASM_ABI_VERSION 0u
#define NARYA_R51_LIMBS 5u
#define NARYA_X8_LANES 8u

typedef enum narya_status {
    NARYA_OK = 0,
    NARYA_ERR_UNSUPPORTED_CPU = 1,
    NARYA_ERR_RANGE = 2,
    NARYA_ERR_INVALID_ARGUMENT = 3,
    NARYA_ERR_NOT_IMPLEMENTED = 4
} narya_status;

/*
 * Structure-of-arrays radix-2^51 field storage.
 *
 * limb[i][lane] is limb i of lane `lane`.  Each composable input limb must
 * be strictly below 2^52.  This is deliberately a public, fixed layout: C,
 * C++, Rust, Zig and hand-written assembly callers can share buffers without
 * marshaling.  The native kernels use unaligned loads, so alignment is not an
 * ABI precondition.
 */
typedef struct narya_r51x8 {
    uint64_t limb[NARYA_R51_LIMBS][NARYA_X8_LANES];
} narya_r51x8;

/* Transposed SHA-512 state and one-block schedule input. */
typedef struct narya_sha512_state_x8 {
    uint64_t word[8][NARYA_X8_LANES];
} narya_sha512_state_x8;

typedef struct narya_sha512_block_x8 {
    uint64_t word[16][NARYA_X8_LANES];
} narya_sha512_block_x8;

/* Reports the complete AVX-512 feature set required by the r51 field layer. */
int narya_r51x8_available(void);

/*
 * Computes eight independent products in F_(2^255-19).
 *
 * The function validates the u52 input contract before entering assembly.
 * `out` may alias `x` or `y`.  On failure, `out` is unchanged.
 * The output is a composable, non-canonical u52 representation; callers may
 * feed it directly to another Narya r51 operation but must not serialize it
 * as a canonical field element without a separate canonicalization step.
 */
narya_status narya_r51x8_mul(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);

/*
 * Composable field addition, subtraction, and negation.  Inputs have the same
 * u52 contract as multiplication; outputs are non-canonical u52 values.
 * Exact source/output aliasing is supported and failures leave `out` intact.
 */
narya_status narya_r51x8_add(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
narya_status narya_r51x8_sub(
    narya_r51x8 *out,
    const narya_r51x8 *x,
    const narya_r51x8 *y);
narya_status narya_r51x8_neg(narya_r51x8 *out, const narya_r51x8 *x);

/*
 * Applies one SHA-512 compression block to eight independent states.
 *
 * block.word[i][lane] is the numeric value of big-endian message word i;
 * callers that start from bytes must byte-swap while transposing.  state and
 * block must not overlap.  On an argument/CPU error state is unchanged.
 * This compression primitive is an ABI-zero review seam, not the eventual
 * segmented R || A || message hashing API.
 */
narya_status narya_sha512_compress_x8(
    narya_sha512_state_x8 *state,
    const narya_sha512_block_x8 *block);

/*
 * Computes SHA-512(original_R || original_A || message) independently in each
 * active lane. R and A contain eight 32-byte rows; message/length select the
 * third segment. Inactive digest rows are zero. A null message pointer is
 * valid only for a zero-length lane. On error the entire digest output is
 * unchanged. This ABI-zero scheduler currently uses the native assembly
 * compression leaf with transparent C padding/transposition.
 */
narya_status narya_sha512_r_a_message_x8(
    uint8_t digest[NARYA_X8_LANES][64],
    const uint8_t r[NARYA_X8_LANES * 32],
    const uint8_t a[NARYA_X8_LANES * 32],
    const uint8_t *const message[NARYA_X8_LANES],
    const size_t length[NARYA_X8_LANES],
    uint8_t active);

/*
 * Reduces eight lane-major 64-byte little-endian integers modulo the
 * Ed25519 group order l. Active outputs are canonical 32-byte little-endian
 * scalars in [0,l); inactive rows are zero. The output may start at the same
 * address as the input because all source bytes are marshaled before stores.
 * On an argument/CPU error the complete output remains unchanged.
 */
narya_status narya_scalar_reduce_x8(
    uint8_t out[NARYA_X8_LANES][32],
    const uint8_t in[NARYA_X8_LANES * 64],
    uint8_t active);

/*
 * Caller-owned scratch required by narya_ed25519_verify_strict_x8. The
 * workspace contains public-key and basepoint tables and may be reused after
 * a call returns. It needs ordinary uint64_t alignment and must not overlap
 * any input or the verdict byte. The exact size is ABI-zero and deliberately
 * queried rather than exposed as a public structure.
 */
size_t narya_ed25519_verify_strict_x8_workspace_size(void);
size_t narya_ed25519_verify_strict_x8_workspace_alignment(void);

/*
 * Verifies up to eight independent Ed25519 signatures under Narya's exact
 * DalekStrict predicate. Public keys are eight 32-byte rows; signatures are
 * eight R||S 64-byte rows. Messages may have unrelated lengths. Inactive
 * lanes are ignored and never appear in the verdict mask.
 *
 * Signature rejection is not an API error: NARYA_OK is returned and the
 * corresponding verdict bit is clear. On an argument/CPU error, verdict_mask
 * is unchanged. This ABI-zero implementation establishes the complete
 * predicate boundary before the fixed-base comb is ported; it is not yet the
 * intended performance implementation.
 */
narya_status narya_ed25519_verify_strict_x8(
    uint8_t *verdict_mask,
    const uint8_t public_key[NARYA_X8_LANES * 32],
    const uint8_t signature[NARYA_X8_LANES * 64],
    const uint8_t *const message[NARYA_X8_LANES],
    const size_t message_length[NARYA_X8_LANES],
    uint8_t active,
    void *workspace,
    size_t workspace_size);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* NARYA_ED25519_ASM_H */
