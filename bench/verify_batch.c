#define _POSIX_C_SOURCE 200809L

/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "narya_ed25519_asm.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef CLOCK_MONOTONIC_RAW
#define CLOCK_MONOTONIC_RAW CLOCK_MONOTONIC
#endif

enum { lanes = 8, maximum = 64, maximum_message = 4096 };

typedef struct fixture {
    uint8_t public_key[32];
    uint8_t signature[64];
    uint8_t message[maximum_message];
    size_t message_length;
} fixture;

static int
hex_nibble(char value)
{
    if (value >= '0' && value <= '9') return value - '0';
    if (value >= 'a' && value <= 'f') return value - 'a' + 10;
    return -1;
}

static int
parse_hex(uint8_t *output, size_t output_size, const char *hex)
{
    if (strlen(hex) != output_size * 2) return 0;
    for (size_t byte = 0; byte < output_size; byte++) {
        const int high = hex_nibble(hex[2 * byte]);
        const int low = hex_nibble(hex[2 * byte + 1]);
        if (high < 0 || low < 0) return 0;
        output[byte] = (uint8_t)(high << 4 | low);
    }
    return 1;
}

static int
load_fixture(const char *path, size_t wanted_lane, fixture *out)
{
    FILE *file = fopen(path, "r");
    if (file == NULL) return 0;
    char line[2 * maximum_message + 512];
    while (fgets(line, sizeof(line), file) != NULL) {
        if (line[0] == '#') continue;
        size_t lane;
        char public_hex[65], signature_hex[129];
        char message_hex[2 * maximum_message + 1];
        if (sscanf(line, "%zu %64s %128s %8192s", &lane, public_hex,
                   signature_hex, message_hex) != 4)
            break;
        if (lane != wanted_lane) continue;
        if (!parse_hex(out->public_key, 32, public_hex) ||
            !parse_hex(out->signature, 64, signature_hex))
            break;
        if (strcmp(message_hex, "-") == 0) {
            out->message_length = 0;
        } else {
            const size_t hex_length = strlen(message_hex);
            if ((hex_length & 1U) != 0 || hex_length / 2 > maximum_message ||
                !parse_hex(out->message, hex_length / 2, message_hex))
                break;
            out->message_length = hex_length / 2;
        }
        fclose(file);
        return 1;
    }
    fclose(file);
    return 0;
}

static uint64_t
nanoseconds(void)
{
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &now) != 0) abort();
    return (uint64_t)now.tv_sec * UINT64_C(1000000000) + (uint64_t)now.tv_nsec;
}

static int
run_padded_x8(
    volatile uint64_t *sink,
    const uint8_t *public_key,
    const uint8_t *signature,
    const uint8_t *const *message,
    const size_t *length,
    size_t count,
    void *workspace,
    size_t workspace_size)
{
    for (size_t offset = 0; offset < count; offset += lanes) {
        const size_t remaining = count - offset;
        const size_t active_lanes = remaining < lanes ? remaining : lanes;
        uint8_t padded_public[lanes * 32] = {0};
        uint8_t padded_signature[lanes * 64] = {0};
        const uint8_t *padded_message[lanes] = {0};
        size_t padded_length[lanes] = {0};
        memcpy(padded_public, &public_key[offset * 32], active_lanes * 32);
        memcpy(padded_signature, &signature[offset * 64], active_lanes * 64);
        for (size_t lane = 0; lane < active_lanes; lane++) {
            padded_message[lane] = message[offset + lane];
            padded_length[lane] = length[offset + lane];
        }
        const uint8_t active = active_lanes == lanes
            ? UINT8_C(0xff)
            : (uint8_t)((UINT16_C(1) << active_lanes) - 1U);
        uint8_t verdict = 0;
        if (narya_ed25519_verify_strict_x8(
                &verdict, padded_public, padded_signature, padded_message,
                padded_length, active, workspace, workspace_size) != NARYA_OK ||
            verdict != active)
            return 0;
        *sink += verdict;
    }
    return 1;
}

static int
run_batch(
    volatile uint64_t *sink,
    const uint8_t *public_key,
    const uint8_t *signature,
    const uint8_t *const *message,
    const size_t *length,
    size_t count,
    void *workspace,
    size_t workspace_size)
{
    uint64_t verdict = 0;
    const uint64_t expected = count == 64
        ? UINT64_MAX
        : (UINT64_C(1) << count) - 1U;
    if (narya_ed25519_verify_strict_batch(
            &verdict, public_key, signature, message, length, count,
            workspace, workspace_size) != NARYA_OK || verdict != expected)
        return 0;
    *sink += verdict;
    return 1;
}

int
main(int argc, char **argv)
{
    if (argc != 6) {
        fprintf(stderr,
            "usage: %s FIXTURE LANE COUNT ITERATIONS SAMPLES\n", argv[0]);
        return 2;
    }
    const size_t fixture_lane = (size_t)strtoull(argv[2], NULL, 10);
    const size_t count = (size_t)strtoull(argv[3], NULL, 10);
    const size_t iterations = (size_t)strtoull(argv[4], NULL, 10);
    const size_t samples = (size_t)strtoull(argv[5], NULL, 10);
    if (fixture_lane >= lanes || count == 0 || count > maximum ||
        iterations == 0 || samples == 0 || !narya_r51x8_available())
        return 2;

    fixture input = {0};
    if (!load_fixture(argv[1], fixture_lane, &input)) return 2;
    uint8_t public_key[maximum * 32], signature[maximum * 64];
    const uint8_t *message[maximum];
    size_t length[maximum];
    for (size_t item = 0; item < count; item++) {
        memcpy(&public_key[item * 32], input.public_key, 32);
        memcpy(&signature[item * 64], input.signature, 64);
        message[item] = input.message;
        length[item] = input.message_length;
    }

    const size_t x8_size = narya_ed25519_verify_strict_x8_workspace_size();
    const size_t batch_size = narya_ed25519_verify_strict_batch_workspace_size();
    void *x8_workspace = malloc(x8_size);
    void *batch_workspace = malloc(batch_size);
    if (x8_workspace == NULL || batch_workspace == NULL) return 2;
    volatile uint64_t sink = 0;
    for (size_t warmup = 0; warmup < 64; warmup++) {
        if (!run_padded_x8(&sink, public_key, signature, message, length, count,
                           x8_workspace, x8_size) ||
            !run_batch(&sink, public_key, signature, message, length, count,
                       batch_workspace, batch_size))
            return 1;
    }
    for (size_t sample = 0; sample < samples; sample++) {
        const int batch_first = (sample & 1U) != 0;
        for (size_t pass = 0; pass < 2; pass++) {
            const int batch = batch_first ? pass == 0 : pass != 0;
            const uint64_t start = nanoseconds();
            for (size_t iteration = 0; iteration < iterations; iteration++) {
                const int ok = batch
                    ? run_batch(&sink, public_key, signature, message, length,
                                count, batch_workspace, batch_size)
                    : run_padded_x8(&sink, public_key, signature, message,
                                    length, count, x8_workspace, x8_size);
                if (!ok) return 1;
            }
            const double ns_batch =
                (double)(nanoseconds() - start) / (double)iterations;
            printf(
                "sample=%zu mode=%s lane=%zu count=%zu ns/batch=%.3f "
                "ns/signature=%.3f\n",
                sample + 1, batch ? "public-batch" : "padded-x8",
                fixture_lane, count, ns_batch, ns_batch / (double)count);
        }
    }
    if (sink == 0) return 1;
    free(x8_workspace);
    free(batch_workspace);
    return 0;
}
