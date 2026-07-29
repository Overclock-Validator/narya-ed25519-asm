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
