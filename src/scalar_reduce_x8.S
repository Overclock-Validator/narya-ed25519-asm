/*
 * Copyright 2026 Overclock Validator
 * SPDX-License-Identifier: Apache-2.0
 *
 * Eight independent reductions modulo the Ed25519 scalar order
 *
 *   l = 2^252 + 27742317777372353535851937790883648493.
 *
 * AUDIT MAP
 * =========
 * ABI
 *   System V AMD64: RDI points to int64_t limbs[24][8]. Every ZMM register
 *   is caller-saved. The leaf has no stack frame and makes no calls.
 *
 * LANE ORIENTATION
 *   ZMMi holds radix-2^21 limb i for eight independent 512-bit inputs. No
 *   shuffle, mask merge, horizontal operation, or shared carry crosses a
 *   lane. Consequently one signature's digest cannot influence another
 *   signature's scalar.
 *
 * SIGNED ARITHMETIC
 *   The reduction deliberately uses signed 64-bit radix-2^21 limbs. VPSRAQ
 *   implements the arithmetic shifts used by the public-domain ref10
 *   schedule. VPMULLQ returns the low 64 bits of a two's-complement product;
 *   docs/proofs/SCALAR_REDUCTION_CONTRACT.md specifies the still-open
 *   instruction-level obligation that every exact intermediate fit int64_t,
 *   so truncation cannot change the integer result. Differential tests are
 *   evidence for this leaf; they are not a completed range certificate.
 *
 * MODULAR FOLD
 *   For a high limb x at position i >= 12, 2^(21i) is replaced using
 *
 *     2^252 =
 *       666643 + 470296*2^21 + 654183*2^42 - 997805*2^63
 *       + 136657*2^84 - 683901*2^105                 (mod l).
 *
 *   FOLD applies this identity and then clears the consumed high limb. The
 *   clear is load-bearing for limb 12: later carries may repopulate it before
 *   a second fold.
 *
 * CANONICALIZATION
 *   Rounded carries first center loose signed limbs. Two final fold/carry
 *   passes leave limbs 0..11 in the unique interval packed by
 *   scalar_reduce.c into a 32-byte representative in [0,l). The result may
 *   use bit 252; in particular, l-1 is not a 252-bit integer.
 *
 * ALIASING
 *   This internal leaf mutates its limb workspace in place. The public
 *   wrapper parses all 512 source bytes before the leaf and does not publish
 *   output until reduction succeeds, which supplies arbitrary source/output
 *   overlap safety and error atomicity at the C ABI.
 *
 * The core schedule is an x8 SysV translation of Narya's fixed-array
 * radix-2^21 reducer. Correctness tests do not reuse this schedule: they use
 * a bit-at-a-time reduction oracle against the literal order l.
 */

.intel_syntax noprefix
.text

/*
 * Fold high into low..low+5. zmm24..29 are positive constants. zmm30 is the
 * sole product temporary, leaving all 24 signed limbs resident in registers.
 */
.macro FOLD high, low0, low1, low2, low3, low4, low5
    vpmullq zmm30, \high, zmm24
    vpaddq \low0, \low0, zmm30
    vpmullq zmm30, \high, zmm25
    vpaddq \low1, \low1, zmm30
    vpmullq zmm30, \high, zmm26
    vpaddq \low2, \low2, zmm30
    vpmullq zmm30, \high, zmm27
    vpsubq \low3, \low3, zmm30
    vpmullq zmm30, \high, zmm28
    vpaddq \low4, \low4, zmm30
    vpmullq zmm30, \high, zmm29
    vpsubq \low5, \low5, zmm30
    vpxorq \high, \high, \high
.endm

/* carry = floor((limb + 2^20)/2^21), matching signed ref10 rounding. */
.macro CARRY_ROUNDED limb, next
    vpaddq zmm30, \limb, zmm31
    vpsraq zmm30, zmm30, 21
    vpaddq \next, \next, zmm30
    vpsllq zmm30, zmm30, 21
    vpsubq \limb, \limb, zmm30
.endm

/* carry = floor(limb/2^21), used by the final canonical carry passes. */
.macro CARRY limb, next
    vpsraq zmm30, \limb, 21
    vpaddq \next, \next, zmm30
    vpsllq zmm30, zmm30, 21
    vpsubq \limb, \limb, zmm30
.endm

.p2align 5
.globl narya_scalar_reduce_radix21_x8_asm
.hidden narya_scalar_reduce_radix21_x8_asm
.type narya_scalar_reduce_radix21_x8_asm, @function
narya_scalar_reduce_radix21_x8_asm:
    /* Keep every limb resident: 24 loads, then no memory until final stores. */
    vmovdqu64 zmm0,  ZMMWORD PTR [rdi +    0]
    vmovdqu64 zmm1,  ZMMWORD PTR [rdi +   64]
    vmovdqu64 zmm2,  ZMMWORD PTR [rdi +  128]
    vmovdqu64 zmm3,  ZMMWORD PTR [rdi +  192]
    vmovdqu64 zmm4,  ZMMWORD PTR [rdi +  256]
    vmovdqu64 zmm5,  ZMMWORD PTR [rdi +  320]
    vmovdqu64 zmm6,  ZMMWORD PTR [rdi +  384]
    vmovdqu64 zmm7,  ZMMWORD PTR [rdi +  448]
    vmovdqu64 zmm8,  ZMMWORD PTR [rdi +  512]
    vmovdqu64 zmm9,  ZMMWORD PTR [rdi +  576]
    vmovdqu64 zmm10, ZMMWORD PTR [rdi +  640]
    vmovdqu64 zmm11, ZMMWORD PTR [rdi +  704]
    vmovdqu64 zmm12, ZMMWORD PTR [rdi +  768]
    vmovdqu64 zmm13, ZMMWORD PTR [rdi +  832]
    vmovdqu64 zmm14, ZMMWORD PTR [rdi +  896]
    vmovdqu64 zmm15, ZMMWORD PTR [rdi +  960]
    vmovdqu64 zmm16, ZMMWORD PTR [rdi + 1024]
    vmovdqu64 zmm17, ZMMWORD PTR [rdi + 1088]
    vmovdqu64 zmm18, ZMMWORD PTR [rdi + 1152]
    vmovdqu64 zmm19, ZMMWORD PTR [rdi + 1216]
    vmovdqu64 zmm20, ZMMWORD PTR [rdi + 1280]
    vmovdqu64 zmm21, ZMMWORD PTR [rdi + 1344]
    vmovdqu64 zmm22, ZMMWORD PTR [rdi + 1408]
    vmovdqu64 zmm23, ZMMWORD PTR [rdi + 1472]

    vpbroadcastq zmm24, QWORD PTR [rip + .Lscalar_666643]
    vpbroadcastq zmm25, QWORD PTR [rip + .Lscalar_470296]
    vpbroadcastq zmm26, QWORD PTR [rip + .Lscalar_654183]
    vpbroadcastq zmm27, QWORD PTR [rip + .Lscalar_997805]
    vpbroadcastq zmm28, QWORD PTR [rip + .Lscalar_136657]
    vpbroadcastq zmm29, QWORD PTR [rip + .Lscalar_683901]

    /* Fold original limbs 23..18 into the still-live 11..17 region. */
    FOLD zmm23, zmm11, zmm12, zmm13, zmm14, zmm15, zmm16
    FOLD zmm22, zmm10, zmm11, zmm12, zmm13, zmm14, zmm15
    FOLD zmm21, zmm9,  zmm10, zmm11, zmm12, zmm13, zmm14
    FOLD zmm20, zmm8,  zmm9,  zmm10, zmm11, zmm12, zmm13
    FOLD zmm19, zmm7,  zmm8,  zmm9,  zmm10, zmm11, zmm12
    FOLD zmm18, zmm6,  zmm7,  zmm8,  zmm9,  zmm10, zmm11

    vpbroadcastq zmm31, QWORD PTR [rip + .Lscalar_round]
    CARRY_ROUNDED zmm6,  zmm7
    CARRY_ROUNDED zmm8,  zmm9
    CARRY_ROUNDED zmm10, zmm11
    CARRY_ROUNDED zmm12, zmm13
    CARRY_ROUNDED zmm14, zmm15
    CARRY_ROUNDED zmm16, zmm17
    CARRY_ROUNDED zmm7,  zmm8
    CARRY_ROUNDED zmm9,  zmm10
    CARRY_ROUNDED zmm11, zmm12
    CARRY_ROUNDED zmm13, zmm14
    CARRY_ROUNDED zmm15, zmm16

    /* Fold the populated limbs 17..12 into the final twelve-limb region. */
    FOLD zmm17, zmm5, zmm6, zmm7, zmm8, zmm9,  zmm10
    FOLD zmm16, zmm4, zmm5, zmm6, zmm7, zmm8,  zmm9
    FOLD zmm15, zmm3, zmm4, zmm5, zmm6, zmm7,  zmm8
    FOLD zmm14, zmm2, zmm3, zmm4, zmm5, zmm6,  zmm7
    FOLD zmm13, zmm1, zmm2, zmm3, zmm4, zmm5,  zmm6
    FOLD zmm12, zmm0, zmm1, zmm2, zmm3, zmm4,  zmm5

    CARRY_ROUNDED zmm0,  zmm1
    CARRY_ROUNDED zmm2,  zmm3
    CARRY_ROUNDED zmm4,  zmm5
    CARRY_ROUNDED zmm6,  zmm7
    CARRY_ROUNDED zmm8,  zmm9
    CARRY_ROUNDED zmm10, zmm11
    CARRY_ROUNDED zmm1,  zmm2
    CARRY_ROUNDED zmm3,  zmm4
    CARRY_ROUNDED zmm5,  zmm6
    CARRY_ROUNDED zmm7,  zmm8
    CARRY_ROUNDED zmm9,  zmm10
    CARRY_ROUNDED zmm11, zmm12

    /*
     * Two fold/carry passes remove a loose coefficient at position 12.
     * They do not require the canonical result to be below 2^252: zmm11 may
     * encode bit 252 after the last carry, as it does for l-1.
     */
    FOLD zmm12, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5
    CARRY zmm0,  zmm1
    CARRY zmm1,  zmm2
    CARRY zmm2,  zmm3
    CARRY zmm3,  zmm4
    CARRY zmm4,  zmm5
    CARRY zmm5,  zmm6
    CARRY zmm6,  zmm7
    CARRY zmm7,  zmm8
    CARRY zmm8,  zmm9
    CARRY zmm9,  zmm10
    CARRY zmm10, zmm11
    CARRY zmm11, zmm12
    FOLD zmm12, zmm0, zmm1, zmm2, zmm3, zmm4, zmm5
    CARRY zmm0,  zmm1
    CARRY zmm1,  zmm2
    CARRY zmm2,  zmm3
    CARRY zmm3,  zmm4
    CARRY zmm4,  zmm5
    CARRY zmm5,  zmm6
    CARRY zmm6,  zmm7
    CARRY zmm7,  zmm8
    CARRY zmm8,  zmm9
    CARRY zmm9,  zmm10
    CARRY zmm10, zmm11

    vmovdqu64 ZMMWORD PTR [rdi +   0], zmm0
    vmovdqu64 ZMMWORD PTR [rdi +  64], zmm1
    vmovdqu64 ZMMWORD PTR [rdi + 128], zmm2
    vmovdqu64 ZMMWORD PTR [rdi + 192], zmm3
    vmovdqu64 ZMMWORD PTR [rdi + 256], zmm4
    vmovdqu64 ZMMWORD PTR [rdi + 320], zmm5
    vmovdqu64 ZMMWORD PTR [rdi + 384], zmm6
    vmovdqu64 ZMMWORD PTR [rdi + 448], zmm7
    vmovdqu64 ZMMWORD PTR [rdi + 512], zmm8
    vmovdqu64 ZMMWORD PTR [rdi + 576], zmm9
    vmovdqu64 ZMMWORD PTR [rdi + 640], zmm10
    vmovdqu64 ZMMWORD PTR [rdi + 704], zmm11
    vzeroupper
    ret
.size narya_scalar_reduce_radix21_x8_asm, .-narya_scalar_reduce_radix21_x8_asm

.section .rodata
.p2align 3
.Lscalar_666643: .quad 666643
.Lscalar_470296: .quad 470296
.Lscalar_654183: .quad 654183
.Lscalar_997805: .quad 997805
.Lscalar_136657: .quad 136657
.Lscalar_683901: .quad 683901
.Lscalar_round:  .quad 1048576

.section .note.GNU-stack,"",@progbits
