/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Eight-lane SHA-512 compression, System V AMD64.
 *
 * AUDIT MAP
 * =========
 * ABI
 *   RDI points to state.word[8][8]; RSI points to block.word[16][8].
 *   ZMM0..ZMM31 and RDX are caller-saved under SysV. The leaf has no stack
 *   frame and executes VZEROUPPER before returning.
 *
 * DATA ORIENTATION
 *   Each ZMM lane is one independent SHA-512 stream. ZMM16..ZMM31 hold the
 *   rolling sixteen-word message schedule; ZMM0..ZMM7 hold a..h. No shuffle,
 *   mask, gather, or horizontal operation crosses lanes.
 *
 * BYTE ORDER
 *   The block contains numeric SHA-512 words, not raw bytes. A caller that
 *   starts from message bytes must load each 64-bit word big-endian while it
 *   transposes eight streams. Keeping that policy out of this leaf lets the
 *   compression differential test message scheduling independently.
 *
 * ROLLING SCHEDULE
 *   For t>=16, W[t mod 16] is replaced only after its old W[t-16] value has
 *   supplied the recurrence. The other three ring positions are W[t-15],
 *   W[t-7], and W[t-2]. This avoids a 5 KiB expanded schedule and all stack
 *   traffic while preserving the FIPS 180-4 recurrence exactly.
 *
 * BOOLEAN FUNCTIONS
 *   VPTERNLOGQ immediate 0xca computes Ch(E,F,G) with old E in the destination;
 *   0xe8 computes Maj(A,B,C); 0x96 computes three-input XOR. Rotates implement
 *   the SHA-512 capital and lowercase sigma functions literally.
 *
 * FEED-FORWARD AND ALIASING
 *   All sixteen block vectors are loaded before state is read. State memory is
 *   not written until all eighty rounds finish, then the original state words
 *   are added. The public ABI nevertheless excludes overlapping state/block
 *   objects so C callers do not rely on a layout accident.
 *
 * This is a SysV/GAS translation of Narya's x8 rolling-register kernel at Go
 * source commit 13dc06d4a5f0ad8be62412a89de3a44de57bd504.
 * Source certificate: docs/proofs/SHA512_SOURCE_SCHEDULE.md.
 * See docs/architecture/SHA512_X8.md for its integration boundary.
 */

.intel_syntax noprefix
.text

.macro SHA512_ROUND A, B, C, D, E, F, G, H, W, KOFF
    /* Sigma1(E). */
    vprorq zmm8, \E, 14
    vprorq zmm9, \E, 18
    vpxorq zmm8, zmm8, zmm9
    vprorq zmm9, \E, 41
    vpxorq zmm8, zmm8, zmm9

    /* Ch(E,F,G): destination starts as E for ternary truth-table input 0. */
    vmovdqa64 zmm10, \E
    vpternlogq zmm10, \F, \G, 0xca
    vpaddq zmm8, zmm8, \H
    vpaddq zmm8, zmm8, zmm10
    vpbroadcastq zmm15, QWORD PTR [rdx + \KOFF]
    vpaddq zmm8, zmm8, zmm15
    vpaddq zmm8, zmm8, \W

    /* Sigma0(A) + Maj(A,B,C). */
    vprorq zmm9, \A, 28
    vprorq zmm11, \A, 34
    vpxorq zmm9, zmm9, zmm11
    vprorq zmm11, \A, 39
    vpxorq zmm9, zmm9, zmm11
    vmovdqa64 zmm10, \A
    vpternlogq zmm10, \B, \C, 0xe8
    vpaddq zmm9, zmm9, zmm10

    /* D becomes E' and H becomes A'; macro arguments rotate next round. */
    vpaddq \D, \D, zmm8
    vpaddq \H, zmm8, zmm9
.endm

.macro SHA512_EXPAND W0, W1, W9, W14
    vprorq zmm12, \W1, 1
    vprorq zmm13, \W1, 8
    vpsrlq zmm14, \W1, 7
    vpternlogq zmm12, zmm13, zmm14, 0x96

    vprorq zmm13, \W14, 19
    vprorq zmm14, \W14, 61
    vpsrlq zmm15, \W14, 6
    vpternlogq zmm13, zmm14, zmm15, 0x96

    vpaddq \W0, \W0, zmm12
    vpaddq \W0, \W0, \W9
    vpaddq \W0, \W0, zmm13
.endm

.p2align 5
.globl narya_sha512_compress_x8_asm
.hidden narya_sha512_compress_x8_asm
.type narya_sha512_compress_x8_asm, @function
narya_sha512_compress_x8_asm:
    /* Load the complete rolling ring before reading or eventually storing state. */
    vmovdqu64 zmm16, ZMMWORD PTR [rsi +   0]
    vmovdqu64 zmm17, ZMMWORD PTR [rsi +  64]
    vmovdqu64 zmm18, ZMMWORD PTR [rsi + 128]
    vmovdqu64 zmm19, ZMMWORD PTR [rsi + 192]
    vmovdqu64 zmm20, ZMMWORD PTR [rsi + 256]
    vmovdqu64 zmm21, ZMMWORD PTR [rsi + 320]
    vmovdqu64 zmm22, ZMMWORD PTR [rsi + 384]
    vmovdqu64 zmm23, ZMMWORD PTR [rsi + 448]
    vmovdqu64 zmm24, ZMMWORD PTR [rsi + 512]
    vmovdqu64 zmm25, ZMMWORD PTR [rsi + 576]
    vmovdqu64 zmm26, ZMMWORD PTR [rsi + 640]
    vmovdqu64 zmm27, ZMMWORD PTR [rsi + 704]
    vmovdqu64 zmm28, ZMMWORD PTR [rsi + 768]
    vmovdqu64 zmm29, ZMMWORD PTR [rsi + 832]
    vmovdqu64 zmm30, ZMMWORD PTR [rsi + 896]
    vmovdqu64 zmm31, ZMMWORD PTR [rsi + 960]

    vmovdqu64 zmm0, ZMMWORD PTR [rdi +   0]
    vmovdqu64 zmm1, ZMMWORD PTR [rdi +  64]
    vmovdqu64 zmm2, ZMMWORD PTR [rdi + 128]
    vmovdqu64 zmm3, ZMMWORD PTR [rdi + 192]
    vmovdqu64 zmm4, ZMMWORD PTR [rdi + 256]
    vmovdqu64 zmm5, ZMMWORD PTR [rdi + 320]
    vmovdqu64 zmm6, ZMMWORD PTR [rdi + 384]
    vmovdqu64 zmm7, ZMMWORD PTR [rdi + 448]
    lea rdx, [rip + narya_sha512_round_constants]

    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm16, 0
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm17, 8
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm18, 16
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm19, 24
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm20, 32
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm21, 40
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm22, 48
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm23, 56
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm24, 64
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm25, 72
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm26, 80
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm27, 88
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm28, 96
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm29, 104
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm30, 112
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm31, 120
    SHA512_EXPAND zmm16, zmm17, zmm25, zmm30
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm16, 128
    SHA512_EXPAND zmm17, zmm18, zmm26, zmm31
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm17, 136
    SHA512_EXPAND zmm18, zmm19, zmm27, zmm16
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm18, 144
    SHA512_EXPAND zmm19, zmm20, zmm28, zmm17
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm19, 152
    SHA512_EXPAND zmm20, zmm21, zmm29, zmm18
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm20, 160
    SHA512_EXPAND zmm21, zmm22, zmm30, zmm19
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm21, 168
    SHA512_EXPAND zmm22, zmm23, zmm31, zmm20
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm22, 176
    SHA512_EXPAND zmm23, zmm24, zmm16, zmm21
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm23, 184
    SHA512_EXPAND zmm24, zmm25, zmm17, zmm22
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm24, 192
    SHA512_EXPAND zmm25, zmm26, zmm18, zmm23
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm25, 200
    SHA512_EXPAND zmm26, zmm27, zmm19, zmm24
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm26, 208
    SHA512_EXPAND zmm27, zmm28, zmm20, zmm25
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm27, 216
    SHA512_EXPAND zmm28, zmm29, zmm21, zmm26
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm28, 224
    SHA512_EXPAND zmm29, zmm30, zmm22, zmm27
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm29, 232
    SHA512_EXPAND zmm30, zmm31, zmm23, zmm28
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm30, 240
    SHA512_EXPAND zmm31, zmm16, zmm24, zmm29
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm31, 248
    SHA512_EXPAND zmm16, zmm17, zmm25, zmm30
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm16, 256
    SHA512_EXPAND zmm17, zmm18, zmm26, zmm31
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm17, 264
    SHA512_EXPAND zmm18, zmm19, zmm27, zmm16
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm18, 272
    SHA512_EXPAND zmm19, zmm20, zmm28, zmm17
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm19, 280
    SHA512_EXPAND zmm20, zmm21, zmm29, zmm18
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm20, 288
    SHA512_EXPAND zmm21, zmm22, zmm30, zmm19
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm21, 296
    SHA512_EXPAND zmm22, zmm23, zmm31, zmm20
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm22, 304
    SHA512_EXPAND zmm23, zmm24, zmm16, zmm21
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm23, 312
    SHA512_EXPAND zmm24, zmm25, zmm17, zmm22
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm24, 320
    SHA512_EXPAND zmm25, zmm26, zmm18, zmm23
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm25, 328
    SHA512_EXPAND zmm26, zmm27, zmm19, zmm24
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm26, 336
    SHA512_EXPAND zmm27, zmm28, zmm20, zmm25
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm27, 344
    SHA512_EXPAND zmm28, zmm29, zmm21, zmm26
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm28, 352
    SHA512_EXPAND zmm29, zmm30, zmm22, zmm27
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm29, 360
    SHA512_EXPAND zmm30, zmm31, zmm23, zmm28
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm30, 368
    SHA512_EXPAND zmm31, zmm16, zmm24, zmm29
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm31, 376
    SHA512_EXPAND zmm16, zmm17, zmm25, zmm30
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm16, 384
    SHA512_EXPAND zmm17, zmm18, zmm26, zmm31
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm17, 392
    SHA512_EXPAND zmm18, zmm19, zmm27, zmm16
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm18, 400
    SHA512_EXPAND zmm19, zmm20, zmm28, zmm17
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm19, 408
    SHA512_EXPAND zmm20, zmm21, zmm29, zmm18
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm20, 416
    SHA512_EXPAND zmm21, zmm22, zmm30, zmm19
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm21, 424
    SHA512_EXPAND zmm22, zmm23, zmm31, zmm20
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm22, 432
    SHA512_EXPAND zmm23, zmm24, zmm16, zmm21
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm23, 440
    SHA512_EXPAND zmm24, zmm25, zmm17, zmm22
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm24, 448
    SHA512_EXPAND zmm25, zmm26, zmm18, zmm23
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm25, 456
    SHA512_EXPAND zmm26, zmm27, zmm19, zmm24
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm26, 464
    SHA512_EXPAND zmm27, zmm28, zmm20, zmm25
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm27, 472
    SHA512_EXPAND zmm28, zmm29, zmm21, zmm26
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm28, 480
    SHA512_EXPAND zmm29, zmm30, zmm22, zmm27
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm29, 488
    SHA512_EXPAND zmm30, zmm31, zmm23, zmm28
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm30, 496
    SHA512_EXPAND zmm31, zmm16, zmm24, zmm29
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm31, 504
    SHA512_EXPAND zmm16, zmm17, zmm25, zmm30
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm16, 512
    SHA512_EXPAND zmm17, zmm18, zmm26, zmm31
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm17, 520
    SHA512_EXPAND zmm18, zmm19, zmm27, zmm16
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm18, 528
    SHA512_EXPAND zmm19, zmm20, zmm28, zmm17
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm19, 536
    SHA512_EXPAND zmm20, zmm21, zmm29, zmm18
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm20, 544
    SHA512_EXPAND zmm21, zmm22, zmm30, zmm19
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm21, 552
    SHA512_EXPAND zmm22, zmm23, zmm31, zmm20
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm22, 560
    SHA512_EXPAND zmm23, zmm24, zmm16, zmm21
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm23, 568
    SHA512_EXPAND zmm24, zmm25, zmm17, zmm22
    SHA512_ROUND zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm24, 576
    SHA512_EXPAND zmm25, zmm26, zmm18, zmm23
    SHA512_ROUND zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm25, 584
    SHA512_EXPAND zmm26, zmm27, zmm19, zmm24
    SHA512_ROUND zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm26, 592
    SHA512_EXPAND zmm27, zmm28, zmm20, zmm25
    SHA512_ROUND zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm4, zmm27, 600
    SHA512_EXPAND zmm28, zmm29, zmm21, zmm26
    SHA512_ROUND zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm3, zmm28, 608
    SHA512_EXPAND zmm29, zmm30, zmm22, zmm27
    SHA512_ROUND zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm2, zmm29, 616
    SHA512_EXPAND zmm30, zmm31, zmm23, zmm28
    SHA512_ROUND zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm1, zmm30, 624
    SHA512_EXPAND zmm31, zmm16, zmm24, zmm29
    SHA512_ROUND zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7, zmm0, zmm31, 632

    /* Davies-Meyer feed-forward from the original state still in memory. */
    vpaddq zmm0, zmm0, ZMMWORD PTR [rdi +   0]
    vpaddq zmm1, zmm1, ZMMWORD PTR [rdi +  64]
    vpaddq zmm2, zmm2, ZMMWORD PTR [rdi + 128]
    vpaddq zmm3, zmm3, ZMMWORD PTR [rdi + 192]
    vpaddq zmm4, zmm4, ZMMWORD PTR [rdi + 256]
    vpaddq zmm5, zmm5, ZMMWORD PTR [rdi + 320]
    vpaddq zmm6, zmm6, ZMMWORD PTR [rdi + 384]
    vpaddq zmm7, zmm7, ZMMWORD PTR [rdi + 448]
    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vmovdqu64 ZMMWORD PTR [rdi + 320], zmm5
    vmovdqu64 ZMMWORD PTR [rdi + 384], zmm6
    vmovdqu64 ZMMWORD PTR [rdi + 448], zmm7
    vzeroupper
    ret
.size narya_sha512_compress_x8_asm, .-narya_sha512_compress_x8_asm

.section .rodata
.p2align 6
narya_sha512_round_constants:
    .quad 0x428a2f98d728ae22
    .quad 0x7137449123ef65cd
    .quad 0xb5c0fbcfec4d3b2f
    .quad 0xe9b5dba58189dbbc
    .quad 0x3956c25bf348b538
    .quad 0x59f111f1b605d019
    .quad 0x923f82a4af194f9b
    .quad 0xab1c5ed5da6d8118
    .quad 0xd807aa98a3030242
    .quad 0x12835b0145706fbe
    .quad 0x243185be4ee4b28c
    .quad 0x550c7dc3d5ffb4e2
    .quad 0x72be5d74f27b896f
    .quad 0x80deb1fe3b1696b1
    .quad 0x9bdc06a725c71235
    .quad 0xc19bf174cf692694
    .quad 0xe49b69c19ef14ad2
    .quad 0xefbe4786384f25e3
    .quad 0x0fc19dc68b8cd5b5
    .quad 0x240ca1cc77ac9c65
    .quad 0x2de92c6f592b0275
    .quad 0x4a7484aa6ea6e483
    .quad 0x5cb0a9dcbd41fbd4
    .quad 0x76f988da831153b5
    .quad 0x983e5152ee66dfab
    .quad 0xa831c66d2db43210
    .quad 0xb00327c898fb213f
    .quad 0xbf597fc7beef0ee4
    .quad 0xc6e00bf33da88fc2
    .quad 0xd5a79147930aa725
    .quad 0x06ca6351e003826f
    .quad 0x142929670a0e6e70
    .quad 0x27b70a8546d22ffc
    .quad 0x2e1b21385c26c926
    .quad 0x4d2c6dfc5ac42aed
    .quad 0x53380d139d95b3df
    .quad 0x650a73548baf63de
    .quad 0x766a0abb3c77b2a8
    .quad 0x81c2c92e47edaee6
    .quad 0x92722c851482353b
    .quad 0xa2bfe8a14cf10364
    .quad 0xa81a664bbc423001
    .quad 0xc24b8b70d0f89791
    .quad 0xc76c51a30654be30
    .quad 0xd192e819d6ef5218
    .quad 0xd69906245565a910
    .quad 0xf40e35855771202a
    .quad 0x106aa07032bbd1b8
    .quad 0x19a4c116b8d2d0c8
    .quad 0x1e376c085141ab53
    .quad 0x2748774cdf8eeb99
    .quad 0x34b0bcb5e19b48a8
    .quad 0x391c0cb3c5c95a63
    .quad 0x4ed8aa4ae3418acb
    .quad 0x5b9cca4f7763e373
    .quad 0x682e6ff3d6b2b8a3
    .quad 0x748f82ee5defb2fc
    .quad 0x78a5636f43172f60
    .quad 0x84c87814a1f0ab72
    .quad 0x8cc702081a6439ec
    .quad 0x90befffa23631e28
    .quad 0xa4506cebde82bde9
    .quad 0xbef9a3f7b2c67915
    .quad 0xc67178f2e372532b
    .quad 0xca273eceea26619c
    .quad 0xd186b8c721c0c207
    .quad 0xeada7dd6cde0eb1e
    .quad 0xf57d4f7fee6ed178
    .quad 0x06f067aa72176fba
    .quad 0x0a637dc5a2c898a6
    .quad 0x113f9804bef90dae
    .quad 0x1b710b35131c471b
    .quad 0x28db77f523047d84
    .quad 0x32caab7b40c72493
    .quad 0x3c9ebe0a15c9bebc
    .quad 0x431d67c49c100d4c
    .quad 0x4cc5d4becb3e42b6
    .quad 0x597f299cfc657e2a
    .quad 0x5fcb6fab3ad6faec
    .quad 0x6c44198c4a475817

.section .note.GNU-stack,"",@progbits
