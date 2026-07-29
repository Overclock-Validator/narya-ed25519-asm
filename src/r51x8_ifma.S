/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Eight-lane radix-2^51 multiplication modulo p = 2^255 - 19.
 *
 * AUDIT MAP
 * =========
 * ABI
 *   System V AMD64: RDI=out, RSI=x, RDX=y.  All vector registers used here
 *   are caller-saved.  The leaf has no stack frame, makes no calls, and ends
 *   with VZEROUPPER before returning to code that may use legacy SSE/AVX.
 *
 * MEMORY LAYOUT
 *   Five consecutive 64-byte vectors, one per radix limb.  A ZMM lane is one
 *   complete and independent field element.  No shuffle or horizontal
 *   operation crosses lanes, so an invalid result cannot cancel another
 *   lane's verification equation.
 *
 * ALIASING
 *   ZMM0..ZMM9 receive all ten source vectors before the first output store.
 *   Therefore out may equal x, y, or both.  Partial overlap is not part of the
 *   public C contract even though many such layouts happen to be safe.
 *
 * RANGE CONTRACT
 *   Every input limb is < 2^52.  VPMADD52 consumes exactly those 52 bits.
 *   The folded convolution limbs are < 2^61.  One parallel carry produces
 *   limb 0 < 2^51 + 19*1024 and limbs 1..4 < 2^51 + 1024, hence every output
 *   is again < 2^52 and is a legal source for the next IFMA operation.
 *
 * SPLIT-PRODUCT RECONSTRUCTION
 *   For a product P, VPMADD52LUQ accumulates l=P mod 2^52 and HUQ accumulates
 *   h=floor(P/2^52).  Since 2^52 = 2*2^51, h belongs in the next radix-2^51
 *   degree with coefficient 2.  COMBINE_HIGH performs that exact adjustment.
 *
 * MODULAR FOLD
 *   B=2^51 and B^5=2^255=19 (mod p).  Degrees 5..9 are multiplied by 19 and
 *   added to degrees 0..4.  The proven bound makes VPMULLQ by 19 exact in
 *   uint64; this is integer arithmetic, not a wrapping shortcut.
 *
 * The longer proof obligations live in docs/proofs/R51_FIELD_CONTRACT.md.
 * tools/generate_r51_mul_trace.py extracts the 25 MUL_PAIR updates,
 * COMBINE_HIGH, FOLD_INTO, NORMALIZE_5 arguments, constants, loads, and stores
 * into GeneratedR51MulTrace.lean. AssemblyTrace.lean consumes that generated
 * output, and radix51_mul_assembly_trace_correct proves the modular result and
 * no-wrap bounds. A second, restricted Lean decoder consumes the exact 800
 * bytes of the canonical linked proof symbol and proves that they decode to
 * the independently expanded 129-instruction source trace. The decoded trace
 * is then executed phase by phase in an unbounded-natural shadow semantics and
 * proved equal to the generated arithmetic output. BitVec range-premise
 * composition, the System V memory/alias theorem, and downstream deployment
 * identity remain open. See
 * docs/proofs/R51_SOURCE_TRACE_REFINEMENT.md and
 * docs/proofs/X86_OBJECT_REFINEMENT_PLAN.md.
 *
 * The add/subtract/negate leaves below are independently extracted by
 * tools/generate_r51_linear_trace.py. LinearTrace.lean proves their exact 4p
 * biases, non-underflow/no-wrap, modular semantics, and composable-u52 output
 * contract. Their emitted-object boundary remains an open obligation; see
 * docs/proofs/X86_OBJECT_REFINEMENT_PLAN.md.
 *
 * This is a SysV/GAS translation of Narya's reviewed Go-ABI Plan 9 leaf at
 * source commit eff4c8ddafdfe0448eb50f2eafc723a42b95fe2c.  The instruction
 * schedule and representation are intentionally kept bit-identical so the
 * standalone port can differential-test against the original implementation.
 */

.intel_syntax noprefix
.text

.macro CLEAR r
    vpxorq \r, \r, \r
.endm

/* l += low52(x*y), h += high52(x*y). */
.macro MUL_PAIR x, y, l, h
    vpmadd52luq \l, \x, \y
    vpmadd52huq \h, \x, \y
.endm

/* Rebase a high-half accumulator into the next radix-2^51 degree. */
.macro COMBINE_HIGH h, l
    vpsllq \h, \h, 1
    vpaddq \l, \l, \h
.endm

/* lo += 19*hi.  tmp must not alias lo, hi or fold19. */
.macro FOLD_INTO lo, hi, tmp, fold19
    vpmullq \tmp, \hi, \fold19
    vpaddq \lo, \lo, \tmp
.endm

/*
 * Parallel carry of the five folded u61 limbs.  Carries are derived from the
 * original inputs before any limb is updated; this detail is part of the
 * exact loose representation and is mirrored by tests/reference_r51x8.c.
 */
.macro NORMALIZE_5 in0, in1, in2, in3, in4, mask, c0, c1, c2, c3, c4, fold19
    vpsrlq \c0, \in0, 51
    vpsrlq \c1, \in1, 51
    vpsrlq \c2, \in2, 51
    vpsrlq \c3, \in3, 51
    vpsrlq \c4, \in4, 51
    vpandq \in0, \in0, \mask
    vpandq \in1, \in1, \mask
    vpandq \in2, \in2, \mask
    vpandq \in3, \in3, \mask
    vpandq \in4, \in4, \mask
    vpaddq \in1, \in1, \c0
    vpaddq \in2, \in2, \c1
    vpaddq \in3, \in3, \c2
    vpaddq \in4, \in4, \c3
    /* c4<2^10, so the low-52 IFMA product is the full integer 19*c4. */
    vpmadd52luq \in0, \fold19, \c4
.endm

.p2align 5
.globl narya_r51x8_mul_ifma
.hidden narya_r51x8_mul_ifma
.type narya_r51x8_mul_ifma, @function
narya_r51x8_mul_ifma:
    /* Load all sources first: this is the alias-safety proof boundary. */
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    vmovdqu64 zmm5, ZMMWORD PTR [rdx +   0]
    vmovdqu64 zmm6, ZMMWORD PTR [rdx +  64]
    vmovdqu64 zmm7, ZMMWORD PTR [rdx + 128]
    vmovdqu64 zmm8, ZMMWORD PTR [rdx + 192]
    vmovdqu64 zmm9, ZMMWORD PTR [rdx + 256]

    /* zmm10..18: low halves of degrees 0..8. */
    /* zmm19..27: high halves of degrees 1..9. */
    CLEAR zmm10
    CLEAR zmm11
    CLEAR zmm12
    CLEAR zmm13
    CLEAR zmm14
    CLEAR zmm15
    CLEAR zmm16
    CLEAR zmm17
    CLEAR zmm18
    CLEAR zmm19
    CLEAR zmm20
    CLEAR zmm21
    CLEAR zmm22
    CLEAR zmm23
    CLEAR zmm24
    CLEAR zmm25
    CLEAR zmm26
    CLEAR zmm27

    /* Full 5x5 schoolbook convolution, independently in every lane. */
    MUL_PAIR zmm0, zmm5, zmm10, zmm19
    MUL_PAIR zmm0, zmm6, zmm11, zmm20
    MUL_PAIR zmm0, zmm7, zmm12, zmm21
    MUL_PAIR zmm0, zmm8, zmm13, zmm22
    MUL_PAIR zmm0, zmm9, zmm14, zmm23
    MUL_PAIR zmm1, zmm5, zmm11, zmm20
    MUL_PAIR zmm1, zmm6, zmm12, zmm21
    MUL_PAIR zmm1, zmm7, zmm13, zmm22
    MUL_PAIR zmm1, zmm8, zmm14, zmm23
    MUL_PAIR zmm1, zmm9, zmm15, zmm24
    MUL_PAIR zmm2, zmm5, zmm12, zmm21
    MUL_PAIR zmm2, zmm6, zmm13, zmm22
    MUL_PAIR zmm2, zmm7, zmm14, zmm23
    MUL_PAIR zmm2, zmm8, zmm15, zmm24
    MUL_PAIR zmm2, zmm9, zmm16, zmm25
    MUL_PAIR zmm3, zmm5, zmm13, zmm22
    MUL_PAIR zmm3, zmm6, zmm14, zmm23
    MUL_PAIR zmm3, zmm7, zmm15, zmm24
    MUL_PAIR zmm3, zmm8, zmm16, zmm25
    MUL_PAIR zmm3, zmm9, zmm17, zmm26
    MUL_PAIR zmm4, zmm5, zmm14, zmm23
    MUL_PAIR zmm4, zmm6, zmm15, zmm24
    MUL_PAIR zmm4, zmm7, zmm16, zmm25
    MUL_PAIR zmm4, zmm8, zmm17, zmm26
    MUL_PAIR zmm4, zmm9, zmm18, zmm27

    COMBINE_HIGH zmm19, zmm11
    COMBINE_HIGH zmm20, zmm12
    COMBINE_HIGH zmm21, zmm13
    COMBINE_HIGH zmm22, zmm14
    COMBINE_HIGH zmm23, zmm15
    COMBINE_HIGH zmm24, zmm16
    COMBINE_HIGH zmm25, zmm17
    COMBINE_HIGH zmm26, zmm18
    vpsllq zmm27, zmm27, 1

    /* Fold radix degrees 5..9 back into 0..4 using B^5 == 19 mod p. */
    vpbroadcastq zmm30, QWORD PTR [rip + narya_ifma_fold19]
    FOLD_INTO zmm10, zmm15, zmm28, zmm30
    FOLD_INTO zmm11, zmm16, zmm28, zmm30
    FOLD_INTO zmm12, zmm17, zmm28, zmm30
    FOLD_INTO zmm13, zmm18, zmm28, zmm30
    FOLD_INTO zmm14, zmm27, zmm28, zmm30

    /* Restore the composable u52 contract with one parallel carry layer. */
    vpbroadcastq zmm5, QWORD PTR [rip + narya_ifma_mask51]
    NORMALIZE_5 zmm10, zmm11, zmm12, zmm13, zmm14, zmm5, \
                zmm15, zmm16, zmm17, zmm18, zmm19, zmm30

    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm10
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm11
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm12
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm13
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm14
    vzeroupper
    ret
.size narya_r51x8_mul_ifma, .-narya_r51x8_mul_ifma

/*
 * Dependent r51x8 square chain for decoder exponentiation.
 *
 * System V AMD64: RDI=out, RSI=x, EDX=count. ZMM0..4 retain the running
 * element across every iteration. A symmetric square needs only five
 * diagonal and ten off-diagonal products; the latter are doubled before the
 * ordinary high-half rebase, fold, and parallel carry. No field state is
 * stored until the complete chain finishes. The output therefore has the
 * same composable-u52 contract as narya_r51x8_mul_ifma, out may equal x, and
 * count zero is an exact copy.
 *
 * This is the SysV/GAS form of Narya's reviewed register-resident decoder
 * square schedule introduced at 1ac9fde456944bb070c1713bf4c3bc8c3e367892.
 */
.p2align 5
.globl narya_r51x8_repeated_square_ifma
.hidden narya_r51x8_repeated_square_ifma
.type narya_r51x8_repeated_square_ifma, @function
narya_r51x8_repeated_square_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    test edx, edx
    je .Lrepeated_square_store

    vpbroadcastq zmm24, QWORD PTR [rip + narya_ifma_mask51]
    vpbroadcastq zmm25, QWORD PTR [rip + narya_ifma_fold19]

.Lrepeated_square_loop:
    CLEAR zmm5
    CLEAR zmm6
    CLEAR zmm7
    CLEAR zmm8
    CLEAR zmm9
    CLEAR zmm10
    CLEAR zmm11
    CLEAR zmm12
    CLEAR zmm13
    CLEAR zmm14
    CLEAR zmm15
    CLEAR zmm16
    CLEAR zmm17
    CLEAR zmm18
    CLEAR zmm19
    CLEAR zmm20
    CLEAR zmm21
    CLEAR zmm22

    /* Accumulate the ten distinct off-diagonal products. */
    MUL_PAIR zmm0, zmm1, zmm6,  zmm15
    MUL_PAIR zmm0, zmm2, zmm7,  zmm16
    MUL_PAIR zmm0, zmm3, zmm8,  zmm17
    MUL_PAIR zmm0, zmm4, zmm9,  zmm18
    MUL_PAIR zmm1, zmm2, zmm8,  zmm17
    MUL_PAIR zmm1, zmm3, zmm9,  zmm18
    MUL_PAIR zmm1, zmm4, zmm10, zmm19
    MUL_PAIR zmm2, zmm3, zmm10, zmm19
    MUL_PAIR zmm2, zmm4, zmm11, zmm20
    MUL_PAIR zmm3, zmm4, zmm12, zmm21

    /* Each off-diagonal term appears twice in a square. */
    vpsllq zmm6,  zmm6,  1
    vpsllq zmm7,  zmm7,  1
    vpsllq zmm8,  zmm8,  1
    vpsllq zmm9,  zmm9,  1
    vpsllq zmm10, zmm10, 1
    vpsllq zmm11, zmm11, 1
    vpsllq zmm12, zmm12, 1
    vpsllq zmm15, zmm15, 1
    vpsllq zmm16, zmm16, 1
    vpsllq zmm17, zmm17, 1
    vpsllq zmm18, zmm18, 1
    vpsllq zmm19, zmm19, 1
    vpsllq zmm20, zmm20, 1
    vpsllq zmm21, zmm21, 1

    /* Add the five diagonal products. */
    MUL_PAIR zmm0, zmm0, zmm5,  zmm14
    MUL_PAIR zmm1, zmm1, zmm7,  zmm16
    MUL_PAIR zmm2, zmm2, zmm9,  zmm18
    MUL_PAIR zmm3, zmm3, zmm11, zmm20
    MUL_PAIR zmm4, zmm4, zmm13, zmm22

    COMBINE_HIGH zmm14, zmm6
    COMBINE_HIGH zmm15, zmm7
    COMBINE_HIGH zmm16, zmm8
    COMBINE_HIGH zmm17, zmm9
    COMBINE_HIGH zmm18, zmm10
    COMBINE_HIGH zmm19, zmm11
    COMBINE_HIGH zmm20, zmm12
    COMBINE_HIGH zmm21, zmm13
    vpsllq zmm22, zmm22, 1

    FOLD_INTO zmm5, zmm10, zmm23, zmm25
    FOLD_INTO zmm6, zmm11, zmm23, zmm25
    FOLD_INTO zmm7, zmm12, zmm23, zmm25
    FOLD_INTO zmm8, zmm13, zmm23, zmm25
    FOLD_INTO zmm9, zmm22, zmm23, zmm25

    NORMALIZE_5 zmm5, zmm6, zmm7, zmm8, zmm9, zmm24, \
                zmm10, zmm11, zmm12, zmm13, zmm14, zmm25

    vmovdqa64 zmm0, zmm5
    vmovdqa64 zmm1, zmm6
    vmovdqa64 zmm2, zmm7
    vmovdqa64 zmm3, zmm8
    vmovdqa64 zmm4, zmm9
    dec edx
    jne .Lrepeated_square_loop

.Lrepeated_square_store:
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vzeroupper
    ret
.size narya_r51x8_repeated_square_ifma, .-narya_r51x8_repeated_square_ifma

/*
 * The three linear operations below use the same parallel carry proven in
 * docs/proofs/R51_FIELD_CONTRACT.md.  Addition produces u53 intermediates.
 * Subtraction and negation first add the radix limbs of 4p:
 *
 *   limb 0: 4*(2^51-19) = 0x001fffffffffffb4
 *   limbs 1..4: 4*(2^51-1) = 0x001ffffffffffffc
 *
 * Since a legal source limb is below 2^52, 4p makes every integer subtraction
 * nonnegative without approaching uint64 overflow.  Adding a multiple of p
 * does not change the represented field element.  All source vectors are
 * consumed before stores begin, so exact in-place operation is safe.
 */

.p2align 5
.globl narya_r51x8_add_ifma
.hidden narya_r51x8_add_ifma
.type narya_r51x8_add_ifma, @function
narya_r51x8_add_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    vpaddq zmm0, zmm0, ZMMWORD PTR [rdx +   0]
    vpaddq zmm1, zmm1, ZMMWORD PTR [rdx +  64]
    vpaddq zmm2, zmm2, ZMMWORD PTR [rdx + 128]
    vpaddq zmm3, zmm3, ZMMWORD PTR [rdx + 192]
    vpaddq zmm4, zmm4, ZMMWORD PTR [rdx + 256]
    vpbroadcastq zmm5, QWORD PTR [rip + narya_ifma_mask51]
    vpbroadcastq zmm11, QWORD PTR [rip + narya_ifma_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm6, zmm7, zmm8, zmm9, zmm10, zmm11
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vzeroupper
    ret
.size narya_r51x8_add_ifma, .-narya_r51x8_add_ifma

.p2align 5
.globl narya_r51x8_sub_ifma
.hidden narya_r51x8_sub_ifma
.type narya_r51x8_sub_ifma, @function
narya_r51x8_sub_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    vpbroadcastq zmm9, QWORD PTR [rip + narya_ifma_sub_bias0]
    vpbroadcastq zmm10, QWORD PTR [rip + narya_ifma_sub_biasn]
    vpaddq zmm0, zmm0, zmm9
    vpaddq zmm1, zmm1, zmm10
    vpaddq zmm2, zmm2, zmm10
    vpaddq zmm3, zmm3, zmm10
    vpaddq zmm4, zmm4, zmm10
    vpsubq zmm0, zmm0, ZMMWORD PTR [rdx +   0]
    vpsubq zmm1, zmm1, ZMMWORD PTR [rdx +  64]
    vpsubq zmm2, zmm2, ZMMWORD PTR [rdx + 128]
    vpsubq zmm3, zmm3, ZMMWORD PTR [rdx + 192]
    vpsubq zmm4, zmm4, ZMMWORD PTR [rdx + 256]
    vpbroadcastq zmm5, QWORD PTR [rip + narya_ifma_mask51]
    vpbroadcastq zmm11, QWORD PTR [rip + narya_ifma_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm6, zmm7, zmm8, zmm9, zmm10, zmm11
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vzeroupper
    ret
.size narya_r51x8_sub_ifma, .-narya_r51x8_sub_ifma

.p2align 5
.globl narya_r51x8_neg_ifma
.hidden narya_r51x8_neg_ifma
.type narya_r51x8_neg_ifma, @function
narya_r51x8_neg_ifma:
    vpbroadcastq zmm0, QWORD PTR [rip + narya_ifma_sub_bias0]
    vpbroadcastq zmm1, QWORD PTR [rip + narya_ifma_sub_biasn]
    vmovdqa64 zmm2, zmm1
    vmovdqa64 zmm3, zmm1
    vmovdqa64 zmm4, zmm1
    vpsubq zmm0, zmm0, ZMMWORD PTR [rsi +   0]
    vpsubq zmm1, zmm1, ZMMWORD PTR [rsi +  64]
    vpsubq zmm2, zmm2, ZMMWORD PTR [rsi + 128]
    vpsubq zmm3, zmm3, ZMMWORD PTR [rsi + 192]
    vpsubq zmm4, zmm4, ZMMWORD PTR [rsi + 256]
    vpbroadcastq zmm5, QWORD PTR [rip + narya_ifma_mask51]
    vpbroadcastq zmm11, QWORD PTR [rip + narya_ifma_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm6, zmm7, zmm8, zmm9, zmm10, zmm11
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vzeroupper
    ret
.size narya_r51x8_neg_ifma, .-narya_r51x8_neg_ifma

.section .rodata
.p2align 3
narya_ifma_mask51:
    .quad 0x0007ffffffffffff
narya_ifma_fold19:
    .quad 19
narya_ifma_sub_bias0:
    .quad 0x001fffffffffffb4
narya_ifma_sub_biasn:
    .quad 0x001ffffffffffffc

.section .note.GNU-stack,"",@progbits
