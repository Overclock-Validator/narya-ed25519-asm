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

#define NARYA_ED25519_ASM_ABI_VERSION 1u
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

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* NARYA_ED25519_ASM_H */
