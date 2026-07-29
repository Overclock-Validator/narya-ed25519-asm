/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Bounded coordinate-permutation and carry leaves for packed_x4.c.
 *
 * One ZMM register contains [X,Y,T,Z,0,0,0,0]. VPERMQ applies its immediate
 * independently to each 256-bit half, so the low half follows the reviewed
 * packed-x4 formula while the zero high half remains zero. These leaves do
 * not implement field multiplication; they bracket the independently proved
 * narya_r51x8_mul_ifma leaf and only perform the point formula's linear maps
 * plus one unsigned carry/fold.
 *
 * This is a SysV/GAS translation of Narya's Go packed stages. The contracts
 * are recorded in docs/architecture/PACKED_SINGLETON.md.
 */
.intel_syntax noprefix
.text

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
    vpmadd52luq \in0, \fold19, \c4
.endm

/* [A,B,C,D] -> [E,G,H,F] for direct-XY Edwards doubling. */
.macro DOUBLE_LINEAR q, bias, t0, t1, t2, zero
    vpermq \t0, \q, 0x57
    vpermq \t1, \q, 0x03
    vpsubq \t2, \t0, \t1
    vpaddq \t0, \t0, \t1
    vpsubq \t1, \zero, \t0
    vmovdqu64 \t2{k1}, \t0
    vmovdqu64 \t2{k2}, \t1
    vpermq \t0, \q, 0xaa
    vpsllq \t0, \t0, 1
    vpsubq \t2{k3}, \t2, \t0
    vpaddq \q, \t2, \bias
.endm

/* [X,Y,T,Z] -> [Y-X,Y+X,T,Z]. */
.macro CACHED_FIRST_LINEAR q, bias, t0, t1
    vpermq \t0, \q, 0xe5
    vpermq \t1, \q, 0x00
    vpsubq \t0{k1}, \t0, \t1
    vpaddq \t0{k2}, \t0, \t1
    vpaddq \q, \t0, \bias
.endm

/* [A,B,C,D] -> [E,G,H,F] for cached Edwards addition. */
.macro CACHED_FINAL_LINEAR q, bias, t0, t1, t2
    vpermq \t0, \q, 0xdd
    vpermq \t1, \q, 0x88
    vpsubq \t2, \t0, \t1
    vpaddq \t0, \t0, \t1
    vpxorq \q, \q, \q
    vmovdqu64 \q{k1}, \t2
    vmovdqu64 \q{k2}, \t0
    vpaddq \q, \q, \bias
.endm

/* The packed final-multiply leaves use the reviewed 25-product r51 schedule. */
.macro MUL_PAIR x, y, low, high
    vpmadd52luq \low, \x, \y
    vpmadd52huq \high, \x, \y
.endm

.macro COMBINE_HIGH high, low
    vpsllq \high, \high, 1
    vpaddq \low, \low, \high
.endm

.macro FOLD_MUL19 low, high, scratch, fold19
    vpmullq \scratch, \high, \fold19
    vpaddq \low, \low, \scratch
.endm

/*
 * Consume normalized [E,G,H,F] in zmm0..zmm4, form the two packed operands
 * with lane-local permutations, multiply them, fold B^5=19, carry once, and
 * store through RDI.  Keeping this boundary in registers removes ten stores
 * and ten reloads from every doubling and cached addition.
 *
 * This multiplication schedule is intentionally character-identical to
 * narya_r51x8_mul_ifma.  Only the source operands are produced in-register.
 */
.macro PACKED_FINAL_MUL_STORE
    vpermq zmm5, zmm0, 0x6b
    vpermq zmm0, zmm0, 0xc4
    vpermq zmm6, zmm1, 0x6b
    vpermq zmm1, zmm1, 0xc4
    vpermq zmm7, zmm2, 0x6b
    vpermq zmm2, zmm2, 0xc4
    vpermq zmm8, zmm3, 0x6b
    vpermq zmm3, zmm3, 0xc4
    vpermq zmm9, zmm4, 0x6b
    vpermq zmm4, zmm4, 0xc4

    vpxorq zmm10, zmm10, zmm10
    vpxorq zmm11, zmm11, zmm11
    vpxorq zmm12, zmm12, zmm12
    vpxorq zmm13, zmm13, zmm13
    vpxorq zmm14, zmm14, zmm14
    vpxorq zmm15, zmm15, zmm15
    vpxorq zmm16, zmm16, zmm16
    vpxorq zmm17, zmm17, zmm17
    vpxorq zmm18, zmm18, zmm18
    vpxorq zmm19, zmm19, zmm19
    vpxorq zmm20, zmm20, zmm20
    vpxorq zmm21, zmm21, zmm21
    vpxorq zmm22, zmm22, zmm22
    vpxorq zmm23, zmm23, zmm23
    vpxorq zmm24, zmm24, zmm24
    vpxorq zmm25, zmm25, zmm25
    vpxorq zmm26, zmm26, zmm26
    vpxorq zmm27, zmm27, zmm27

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

    vpbroadcastq zmm30, QWORD PTR [rip + packed_fold19]
    FOLD_MUL19 zmm10, zmm15, zmm28, zmm30
    FOLD_MUL19 zmm11, zmm16, zmm28, zmm30
    FOLD_MUL19 zmm12, zmm17, zmm28, zmm30
    FOLD_MUL19 zmm13, zmm18, zmm28, zmm30
    FOLD_MUL19 zmm14, zmm27, zmm28, zmm30

    vpbroadcastq zmm5, QWORD PTR [rip + packed_mask51]
    NORMALIZE_5 zmm10, zmm11, zmm12, zmm13, zmm14, zmm5, \
                zmm15, zmm16, zmm17, zmm18, zmm19, zmm30
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm10
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm11
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm12
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm13
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm14
.endm

.p2align 5
.globl narya_packed_double_first_operands_ifma
.hidden narya_packed_double_first_operands_ifma
.type narya_packed_double_first_operands_ifma, @function
narya_packed_double_first_operands_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rdx +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rdx +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rdx + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rdx + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rdx + 256]
    vpermq zmm5, zmm0, 0x34
    vpermq zmm6, zmm0, 0x74
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm5
    vmovdqu64 ZMMWORD PTR [rsi +   0], zmm6
    vpermq zmm5, zmm1, 0x34
    vpermq zmm6, zmm1, 0x74
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm5
    vmovdqu64 ZMMWORD PTR [rsi +  64], zmm6
    vpermq zmm5, zmm2, 0x34
    vpermq zmm6, zmm2, 0x74
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm5
    vmovdqu64 ZMMWORD PTR [rsi + 128], zmm6
    vpermq zmm5, zmm3, 0x34
    vpermq zmm6, zmm3, 0x74
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm5
    vmovdqu64 ZMMWORD PTR [rsi + 192], zmm6
    vpermq zmm5, zmm4, 0x34
    vpermq zmm6, zmm4, 0x74
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm5
    vmovdqu64 ZMMWORD PTR [rsi + 256], zmm6
    vzeroupper
    ret
.size narya_packed_double_first_operands_ifma, .-narya_packed_double_first_operands_ifma

.p2align 5
.globl narya_packed_cached_first_operand_ifma
.hidden narya_packed_cached_first_operand_ifma
.type narya_packed_cached_first_operand_ifma, @function
narya_packed_cached_first_operand_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    mov eax, 0x11
    kmovb k1, eax
    mov eax, 0x22
    kmovb k2, eax
    vmovdqu64 zmm5, ZMMWORD PTR [rip + packed_cached_first_bias0]
    CACHED_FIRST_LINEAR zmm0, zmm5, zmm7, zmm8
    vmovdqu64 zmm5, ZMMWORD PTR [rip + packed_cached_first_biasn]
    CACHED_FIRST_LINEAR zmm1, zmm5, zmm7, zmm8
    CACHED_FIRST_LINEAR zmm2, zmm5, zmm7, zmm8
    CACHED_FIRST_LINEAR zmm3, zmm5, zmm7, zmm8
    CACHED_FIRST_LINEAR zmm4, zmm5, zmm7, zmm8
    vpbroadcastq zmm5, QWORD PTR [rip + packed_mask51]
    vpbroadcastq zmm11, QWORD PTR [rip + packed_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm6, zmm7, zmm8, zmm9, zmm10, zmm11
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vzeroupper
    ret
.size narya_packed_cached_first_operand_ifma, .-narya_packed_cached_first_operand_ifma

.p2align 5
.globl narya_packed_double_final_operands_ifma
.hidden narya_packed_double_final_operands_ifma
.type narya_packed_double_final_operands_ifma, @function
narya_packed_double_final_operands_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rdx +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rdx +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rdx + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rdx + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rdx + 256]
    mov eax, 0x11
    kmovb k1, eax
    mov eax, 0x44
    kmovb k2, eax
    mov eax, 0x88
    kmovb k3, eax
    vmovdqu64 zmm5, ZMMWORD PTR [rip + packed_double_bias8p0]
    vmovdqu64 zmm6, ZMMWORD PTR [rip + packed_double_bias8pn]
    vpxorq zmm7, zmm7, zmm7
    DOUBLE_LINEAR zmm0, zmm5, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm1, zmm6, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm2, zmm6, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm3, zmm6, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm4, zmm6, zmm8, zmm9, zmm10, zmm7
    vpbroadcastq zmm5, QWORD PTR [rip + packed_mask51]
    vpbroadcastq zmm6, QWORD PTR [rip + packed_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm7, zmm8, zmm9, zmm10, zmm11, zmm6
    vpermq zmm12, zmm0, 0xc4
    vpermq zmm13, zmm0, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm12
    vmovdqu64 ZMMWORD PTR [rsi +   0], zmm13
    vpermq zmm12, zmm1, 0xc4
    vpermq zmm13, zmm1, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm12
    vmovdqu64 ZMMWORD PTR [rsi +  64], zmm13
    vpermq zmm12, zmm2, 0xc4
    vpermq zmm13, zmm2, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm12
    vmovdqu64 ZMMWORD PTR [rsi + 128], zmm13
    vpermq zmm12, zmm3, 0xc4
    vpermq zmm13, zmm3, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm12
    vmovdqu64 ZMMWORD PTR [rsi + 192], zmm13
    vpermq zmm12, zmm4, 0xc4
    vpermq zmm13, zmm4, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm12
    vmovdqu64 ZMMWORD PTR [rsi + 256], zmm13
    vzeroupper
    ret
.size narya_packed_double_final_operands_ifma, .-narya_packed_double_final_operands_ifma

.p2align 5
.globl narya_packed_cached_final_operands_ifma
.hidden narya_packed_cached_final_operands_ifma
.type narya_packed_cached_final_operands_ifma, @function
narya_packed_cached_final_operands_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rdx +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rdx +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rdx + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rdx + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rdx + 256]
    mov eax, 0x99
    kmovb k1, eax
    mov eax, 0x66
    kmovb k2, eax
    vmovdqu64 zmm5, ZMMWORD PTR [rip + packed_cached_final_bias8p0]
    vmovdqu64 zmm6, ZMMWORD PTR [rip + packed_cached_final_bias8pn]
    CACHED_FINAL_LINEAR zmm0, zmm5, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm1, zmm6, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm2, zmm6, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm3, zmm6, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm4, zmm6, zmm7, zmm8, zmm9
    vpbroadcastq zmm5, QWORD PTR [rip + packed_mask51]
    vpbroadcastq zmm6, QWORD PTR [rip + packed_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm7, zmm8, zmm9, zmm10, zmm11, zmm6
    vpermq zmm12, zmm0, 0xc4
    vpermq zmm13, zmm0, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm12
    vmovdqu64 ZMMWORD PTR [rsi +   0], zmm13
    vpermq zmm12, zmm1, 0xc4
    vpermq zmm13, zmm1, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm12
    vmovdqu64 ZMMWORD PTR [rsi +  64], zmm13
    vpermq zmm12, zmm2, 0xc4
    vpermq zmm13, zmm2, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm12
    vmovdqu64 ZMMWORD PTR [rsi + 128], zmm13
    vpermq zmm12, zmm3, 0xc4
    vpermq zmm13, zmm3, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm12
    vmovdqu64 ZMMWORD PTR [rsi + 192], zmm13
    vpermq zmm12, zmm4, 0xc4
    vpermq zmm13, zmm4, 0x6b
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm12
    vmovdqu64 ZMMWORD PTR [rsi + 256], zmm13
    vzeroupper
    ret
.size narya_packed_cached_final_operands_ifma, .-narya_packed_cached_final_operands_ifma

/*
 * Fused doubling tail.  The split form above remains as a small differential
 * oracle, while the hot path consumes [A,B,C,D] and emits [X,Y,T,Z] without
 * materializing the two final multiplication operands in memory.
 */
.p2align 6
.globl narya_packed_double_final_multiply_ifma
.hidden narya_packed_double_final_multiply_ifma
.type narya_packed_double_final_multiply_ifma, @function
narya_packed_double_final_multiply_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    mov eax, 0x11
    kmovb k1, eax
    mov eax, 0x44
    kmovb k2, eax
    mov eax, 0x88
    kmovb k3, eax
    vmovdqu64 zmm5, ZMMWORD PTR [rip + packed_double_bias8p0]
    vmovdqu64 zmm6, ZMMWORD PTR [rip + packed_double_bias8pn]
    vpxorq zmm7, zmm7, zmm7
    DOUBLE_LINEAR zmm0, zmm5, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm1, zmm6, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm2, zmm6, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm3, zmm6, zmm8, zmm9, zmm10, zmm7
    DOUBLE_LINEAR zmm4, zmm6, zmm8, zmm9, zmm10, zmm7
    vpbroadcastq zmm5, QWORD PTR [rip + packed_mask51]
    vpbroadcastq zmm6, QWORD PTR [rip + packed_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm7, zmm8, zmm9, zmm10, zmm11, zmm6
    PACKED_FINAL_MUL_STORE
    vzeroupper
    ret
.size narya_packed_double_final_multiply_ifma, .-narya_packed_double_final_multiply_ifma

/* Cached-add analogue of narya_packed_double_final_multiply_ifma. */
.p2align 6
.globl narya_packed_cached_final_multiply_ifma
.hidden narya_packed_cached_final_multiply_ifma
.type narya_packed_cached_final_multiply_ifma, @function
narya_packed_cached_final_multiply_ifma:
    vmovdqu64 zmm0, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rsi + 256]
    mov eax, 0x99
    kmovb k1, eax
    mov eax, 0x66
    kmovb k2, eax
    vmovdqu64 zmm5, ZMMWORD PTR [rip + packed_cached_final_bias8p0]
    vmovdqu64 zmm6, ZMMWORD PTR [rip + packed_cached_final_bias8pn]
    CACHED_FINAL_LINEAR zmm0, zmm5, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm1, zmm6, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm2, zmm6, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm3, zmm6, zmm7, zmm8, zmm9
    CACHED_FINAL_LINEAR zmm4, zmm6, zmm7, zmm8, zmm9
    vpbroadcastq zmm5, QWORD PTR [rip + packed_mask51]
    vpbroadcastq zmm6, QWORD PTR [rip + packed_fold19]
    NORMALIZE_5 zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, \
                zmm7, zmm8, zmm9, zmm10, zmm11, zmm6
    PACKED_FINAL_MUL_STORE
    vzeroupper
    ret
.size narya_packed_cached_final_multiply_ifma, .-narya_packed_cached_final_multiply_ifma

.section .rodata
.p2align 6
packed_mask51:
    .quad 0x0007ffffffffffff
packed_fold19:
    .quad 19

packed_cached_first_bias0:
    .quad 0x001fffffffffffb4, 0, 0, 0
    .quad 0x001fffffffffffb4, 0, 0, 0
packed_cached_first_biasn:
    .quad 0x001ffffffffffffc, 0, 0, 0
    .quad 0x001ffffffffffffc, 0, 0, 0
packed_double_bias8p0:
    .quad 0, 0x003fffffffffff68, 0x003fffffffffff68, 0x003fffffffffff68
    .quad 0, 0x003fffffffffff68, 0x003fffffffffff68, 0x003fffffffffff68
packed_double_bias8pn:
    .quad 0, 0x003ffffffffffff8, 0x003ffffffffffff8, 0x003ffffffffffff8
    .quad 0, 0x003ffffffffffff8, 0x003ffffffffffff8, 0x003ffffffffffff8
packed_cached_final_bias8p0:
    .quad 0x003fffffffffff68, 0, 0, 0x003fffffffffff68
    .quad 0x003fffffffffff68, 0, 0, 0x003fffffffffff68
packed_cached_final_bias8pn:
    .quad 0x003ffffffffffff8, 0, 0, 0x003ffffffffffff8
    .quad 0x003ffffffffffff8, 0, 0, 0x003ffffffffffff8

.section .note.GNU-stack,"",@progbits
