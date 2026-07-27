/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "narya_ed25519_asm.h"

#if defined(__x86_64__) || defined(_M_X64)

#if defined(__GNUC__) || defined(__clang__)
#include <cpuid.h>

static uint64_t
narya_xgetbv0(void)
{
    uint32_t eax;
    uint32_t edx;
    __asm__ volatile("xgetbv" : "=a"(eax), "=d"(edx) : "c"(0));
    return ((uint64_t)edx << 32) | eax;
}

int
narya_r51x8_available(void)
{
    unsigned int eax;
    unsigned int ebx;
    unsigned int ecx;
    unsigned int edx;

    if (__get_cpuid_max(0, NULL) < 7)
        return 0;
    if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx))
        return 0;

    /* AVX and OSXSAVE are prerequisites for asking the OS to preserve ZMM. */
    if ((ecx & bit_AVX) == 0 || (ecx & bit_OSXSAVE) == 0)
        return 0;

    /* XMM, YMM, opmask, ZMM_hi256 and hi16_ZMM must all be OS-enabled. */
    const uint64_t required_xcr0 =
        (UINT64_C(1) << 1) | (UINT64_C(1) << 2) |
        (UINT64_C(1) << 5) | (UINT64_C(1) << 6) |
        (UINT64_C(1) << 7);
    if ((narya_xgetbv0() & required_xcr0) != required_xcr0)
        return 0;

    __cpuid_count(7, 0, eax, ebx, ecx, edx);

    /*
     * This mirrors the reviewed Narya r51 gate rather than detecting only
     * instructions used by this first leaf.  Later point, selector and decode
     * kernels may rely on F, VL, DQ, BW, IFMA and VBMI; accepting a narrower
     * CPU here would turn feature safety into a call-order property.
     */
    const unsigned int required_ebx =
        (UINT32_C(1) << 16) | /* AVX512F */
        (UINT32_C(1) << 17) | /* AVX512DQ */
        (UINT32_C(1) << 21) | /* AVX512IFMA */
        (UINT32_C(1) << 30) | /* AVX512BW */
        (UINT32_C(1) << 31);  /* AVX512VL */
    const unsigned int required_ecx = UINT32_C(1) << 1; /* AVX512VBMI */

    return (ebx & required_ebx) == required_ebx &&
           (ecx & required_ecx) == required_ecx;
}

#else
int narya_r51x8_available(void) { return 0; }
#endif

#else
int narya_r51x8_available(void) { return 0; }
#endif
