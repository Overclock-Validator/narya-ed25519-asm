/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Eight-key affine-Niels micro-AoS to arithmetic-SoA transpose.
 *
 * ABI
 *   SysV AMD64: RDI=out, RSI=&source[0]. No stack and no calls. Only
 *   caller-saved GPRs, YMM0..7 and K1 are modified. VZEROUPPER precedes RET.
 *
 * INPUT
 *   Each source is exactly 120 bytes: five 24-byte rows of
 *   [Y+X,Y-X,2dT]. K1=0b0111 makes every VMOVDQU64 load exactly three qwords;
 *   in particular the row at offset 96 cannot overread the entry boundary.
 *
 * OUTPUT
 *   Three narya_r51x8 coordinates occupy offsets 0, 320 and 640. Each output
 *   lane comes from the corresponding source pointer; shuffles only transpose
 *   representation and never combine lane values arithmetically.
 *
 * ALIAS
 *   Source entries and output must not overlap. The selector supplies a
 *   separate output object. All four source rows for a half are loaded before
 *   stores from that half.
 *
 * Source schedule: Narya Go commit 13dc06d4a5f0ad8be62412a89de3a44de57bd504.
 * Proof boundary: docs/proofs/TRANSPOSE_LANE_MAP.md.
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

.macro TRANSPOSE_HALF source_offset, output_offset, p0, p1, p2, p3
    vmovdqu64 ymm0{k1}{z}, YMMWORD PTR [\p0 + \source_offset]
    vmovdqu64 ymm1{k1}{z}, YMMWORD PTR [\p1 + \source_offset]
    vmovdqu64 ymm2{k1}{z}, YMMWORD PTR [\p2 + \source_offset]
    vmovdqu64 ymm3{k1}{z}, YMMWORD PTR [\p3 + \source_offset]
    TRANSPOSE_4X4
    vmovdqu YMMWORD PTR [rax + \output_offset], ymm0
    vmovdqu YMMWORD PTR [rax + 320 + \output_offset], ymm1
    vmovdqu YMMWORD PTR [rax + 640 + \output_offset], ymm2
.endm

.p2align 5
.globl narya_affine_niels_transpose_x8_asm
.hidden narya_affine_niels_transpose_x8_asm
.type narya_affine_niels_transpose_x8_asm, @function
narya_affine_niels_transpose_x8_asm:
    mov eax, 7
    kmovb k1, eax
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
    TRANSPOSE_HALF 24, 64, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 24, 96, r10, r11, rdi, rsi
    TRANSPOSE_HALF 48, 128, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 48, 160, r10, r11, rdi, rsi
    TRANSPOSE_HALF 72, 192, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 72, 224, r10, r11, rdi, rsi
    TRANSPOSE_HALF 96, 256, rdx, rcx, r8,  r9
    TRANSPOSE_HALF 96, 288, r10, r11, rdi, rsi
    vzeroupper
    ret
.size narya_affine_niels_transpose_x8_asm, .-narya_affine_niels_transpose_x8_asm

.section .note.GNU-stack,"",@progbits
