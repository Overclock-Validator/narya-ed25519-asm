/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Eight-key micro-AoS to arithmetic-SoA transpose.
 *
 * AUDIT MAP
 * =========
 * ABI
 *   System V AMD64: RDI=out, RSI=&source[0]. The leaf loads the eight source
 *   pointers into caller-saved GPRs, uses only YMM0..7, has no stack frame,
 *   makes no calls, and returns through VZEROUPPER.
 *
 * SOURCE LAYOUT
 *   Each 160-byte source contains five 32-byte rows. Within a row the four
 *   qwords are [Y+X,Y-X,Z,2dT] for one key and one already-selected sign and
 *   magnitude. Four source rows therefore form a 4x4 qword matrix.
 *
 * OUTPUT LAYOUT
 *   One arithmetic coordinate is five 64-byte limb vectors. Lanes 0..3 come
 *   from the first four sources and lanes 4..7 from the second four. The
 *   transpose writes Y+X at offset 0, Y-X at 320, Z at 640, and 2dT at 960.
 *   In closed form, coordinate q, limb j, lane i is written at byte
 *   320*q + 64*j + 8*i and equals source[i]->limb[j][q].
 *
 * NONINTERFERENCE
 *   The 4x4 shuffles permute qwords only to change representation; they never
 *   combine them arithmetically. Every output lane is exactly one input key's
 *   selected coordinate. Tests fill every source cell with a distinct tag and
 *   exercise all masks, signs, magnitudes, and identity lanes.
 *
 * ALIASING
 *   Sources and output must not overlap. The table selector owns a separate
 *   output object, so this is an internal construction invariant rather than
 *   a public caller obligation.
 *
 * This is a SysV/GAS translation of Narya's reviewed Go-ABI selector at
 * commit 13dc06d4a5f0ad8be62412a89de3a44de57bd504.
 * Machine-checked lane map and source binding:
 *   docs/proofs/TRANSPOSE_LANE_MAP.md
 */

.intel_syntax noprefix
.text

.macro TRANSPOSE_4X4
    vpunpcklqdq ymm4, ymm0, ymm1
    vpunpckhqdq ymm5, ymm0, ymm1
    vpunpcklqdq ymm6, ymm2, ymm3
    vpunpckhqdq ymm7, ymm2, ymm3
    vshufi64x2 ymm0, ymm4, ymm6, 0x00
    vshufi64x2 ymm1, ymm5, ymm7, 0x00
    vshufi64x2 ymm2, ymm4, ymm6, 0x03
    vshufi64x2 ymm3, ymm5, ymm7, 0x03
.endm

/* Load one limb from four keys and place its four coordinates in HALF. */
.macro TRANSPOSE_HALF off, half, p0, p1, p2, p3
    vmovdqu ymm0, YMMWORD PTR [\p0 + \off]
    vmovdqu ymm1, YMMWORD PTR [\p1 + \off]
    vmovdqu ymm2, YMMWORD PTR [\p2 + \off]
    vmovdqu ymm3, YMMWORD PTR [\p3 + \off]
    TRANSPOSE_4X4
    vmovdqu YMMWORD PTR [rax + 2*\off + \half], ymm0
    vmovdqu YMMWORD PTR [rax + 320 + 2*\off + \half], ymm1
    vmovdqu YMMWORD PTR [rax + 640 + 2*\off + \half], ymm2
    vmovdqu YMMWORD PTR [rax + 960 + 2*\off + \half], ymm3
.endm

.p2align 5
.globl narya_projective_niels_transpose_x8_asm
.hidden narya_projective_niels_transpose_x8_asm
.type narya_projective_niels_transpose_x8_asm, @function
narya_projective_niels_transpose_x8_asm:
    mov rax, rdi
    mov rdx, QWORD PTR [rsi + 0]
    mov rcx, QWORD PTR [rsi + 8]
    mov r8,  QWORD PTR [rsi + 16]
    mov r9,  QWORD PTR [rsi + 24]
    mov r10, QWORD PTR [rsi + 32]
    mov r11, QWORD PTR [rsi + 40]
    mov rdi, QWORD PTR [rsi + 48]
    mov rsi, QWORD PTR [rsi + 56]

    TRANSPOSE_HALF 0,   0, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 0,  32, r10, r11, rdi, rsi
    TRANSPOSE_HALF 32,  0, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 32, 32, r10, r11, rdi, rsi
    TRANSPOSE_HALF 64,  0, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 64, 32, r10, r11, rdi, rsi
    TRANSPOSE_HALF 96,  0, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 96, 32, r10, r11, rdi, rsi
    TRANSPOSE_HALF 128,  0, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 128, 32, r10, r11, rdi, rsi
    vzeroupper
    ret
.size narya_projective_niels_transpose_x8_asm, .-narya_projective_niels_transpose_x8_asm

.section .note.GNU-stack,"",@progbits
