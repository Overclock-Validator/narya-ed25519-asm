/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

extern void narya_projective_niels_transpose_x8_asm(void *out, const void *source[8]);
extern void narya_affine_niels_transpose_x8_asm(void *out, const void *source[8]);

#if defined(__x86_64__)
static void cpuid(uint32_t leaf, uint32_t subleaf,
                  uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d) {
    __asm__ volatile("cpuid"
                     : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d)
                     : "a"(leaf), "c"(subleaf));
}

static uint64_t xgetbv0(void) {
    uint32_t lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    return ((uint64_t)hi << 32) | lo;
}

static int transpose_isa_available(void) {
    uint32_t a, b, c, d;
    cpuid(1, 0, &a, &b, &c, &d);
    if ((c & (1u << 27)) == 0 || (c & (1u << 28)) == 0)
        return 0;
    if ((xgetbv0() & UINT64_C(0xe6)) != UINT64_C(0xe6))
        return 0;
    cpuid(7, 0, &a, &b, &c, &d);
    return (b & (1u << 16)) != 0 &&
           (b & (1u << 17)) != 0 &&
           (b & (1u << 31)) != 0;
}
#else
static int transpose_isa_available(void) { return 0; }
#endif

static uint64_t tag(unsigned lane, unsigned limb, unsigned coordinate) {
    return UINT64_C(0x4e41525941000000) |
           ((uint64_t)lane << 16) |
           ((uint64_t)limb << 8) |
           coordinate;
}

static int test_projective(void) {
    uint64_t source_storage[8][5][4];
    const void *sources[8];
    uint64_t output[4][5][8];
    memset(output, 0xa5, sizeof(output));
    for (unsigned lane = 0; lane < 8; lane++) {
        sources[lane] = source_storage[lane];
        for (unsigned limb = 0; limb < 5; limb++)
            for (unsigned coordinate = 0; coordinate < 4; coordinate++)
                source_storage[lane][limb][coordinate] = tag(lane, limb, coordinate);
    }
    narya_projective_niels_transpose_x8_asm(output, sources);
    for (unsigned coordinate = 0; coordinate < 4; coordinate++)
        for (unsigned limb = 0; limb < 5; limb++)
            for (unsigned lane = 0; lane < 8; lane++)
                if (output[coordinate][limb][lane] != tag(lane, limb, coordinate)) {
                    fprintf(stderr, "projective mismatch q=%u limb=%u lane=%u\n",
                            coordinate, limb, lane);
                    return 0;
                }
    return 1;
}

static int test_affine_guard_page(void) {
    const long page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0 || page_size < 128)
        return 0;
    void *mappings[8] = {0};
    const void *sources[8] = {0};
    uint64_t output[3][5][8];
    memset(output, 0xa5, sizeof(output));

    for (unsigned lane = 0; lane < 8; lane++) {
        uint8_t *mapping = mmap(NULL, (size_t)page_size * 2,
            PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (mapping == MAP_FAILED) {
            perror("mmap");
            return 0;
        }
        mappings[lane] = mapping;
        if (mprotect(mapping + page_size, (size_t)page_size, PROT_NONE) != 0) {
            perror("mprotect");
            return 0;
        }
        uint64_t *source = (uint64_t *)(mapping + page_size - 120);
        sources[lane] = source;
        for (unsigned limb = 0; limb < 5; limb++)
            for (unsigned coordinate = 0; coordinate < 3; coordinate++)
                source[3 * limb + coordinate] = tag(lane, limb, coordinate);
    }

    /* The final masked load addresses source+96 through source+127.  Its fourth
       qword is entirely in PROT_NONE; K1=0b0111 must suppress that fault. */
    narya_affine_niels_transpose_x8_asm(output, sources);

    int ok = 1;
    for (unsigned coordinate = 0; coordinate < 3; coordinate++)
        for (unsigned limb = 0; limb < 5; limb++)
            for (unsigned lane = 0; lane < 8; lane++)
                if (output[coordinate][limb][lane] != tag(lane, limb, coordinate)) {
                    fprintf(stderr, "affine mismatch q=%u limb=%u lane=%u\n",
                            coordinate, limb, lane);
                    ok = 0;
                }
    for (unsigned lane = 0; lane < 8; lane++)
        if (mappings[lane] != NULL)
            munmap(mappings[lane], (size_t)page_size * 2);
    return ok;
}

int main(void) {
    if (!transpose_isa_available()) {
        const char *required = getenv("NARYA_REQUIRE_IFMA");
        if (required != NULL && required[0] == '1') {
            fputs("AVX-512F/DQ/VL and OS ZMM state required\n", stderr);
            return 1;
        }
        puts("SKIP: AVX-512F/DQ/VL or OS ZMM state unavailable");
        return 0;
    }
    if (!test_projective() || !test_affine_guard_page())
        return 1;
    puts("PASS: whole-leaf transpose lane maps and affine guard-page tail");
    return 0;
}
