#define _POSIX_C_SOURCE 200809L

#include "narya_ed25519_asm.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { lanes = 8, maximum_message = 4096 };

typedef struct verify_fixture {
    uint8_t public_key[32];
    uint8_t signature[64];
    uint8_t message[maximum_message];
    size_t message_length;
} verify_fixture;

static int
hex_nibble(char value)
{
    if (value >= '0' && value <= '9')
        return value - '0';
    if (value >= 'a' && value <= 'f')
        return value - 'a' + 10;
    return -1;
}

static int
parse_hex(uint8_t *output, size_t output_size, const char *hex)
{
    if (strlen(hex) != output_size * 2)
        return 0;
    for (size_t byte = 0; byte < output_size; byte++) {
        const int high = hex_nibble(hex[2 * byte]);
        const int low = hex_nibble(hex[2 * byte + 1]);
        if (high < 0 || low < 0)
            return 0;
        output[byte] = (uint8_t)(high << 4 | low);
    }
    return 1;
}

static int
load_fixture(const char *path, verify_fixture fixture[lanes])
{
    FILE *file = fopen(path, "r");
    if (file == NULL)
        return 0;
    uint8_t seen = 0;
    char line[2 * maximum_message + 512];
    while (fgets(line, sizeof(line), file) != NULL) {
        if (line[0] == '#')
            continue;
        size_t lane;
        char public_hex[65], signature_hex[129];
        char message_hex[2 * maximum_message + 1];
        if (sscanf(line, "%zu %64s %128s %8192s", &lane, public_hex,
                   signature_hex, message_hex) != 4 ||
            lane >= lanes ||
            !parse_hex(fixture[lane].public_key, 32, public_hex) ||
            !parse_hex(fixture[lane].signature, 64, signature_hex)) {
            fclose(file);
            return 0;
        }
        if (strcmp(message_hex, "-") == 0) {
            fixture[lane].message_length = 0;
        } else {
            const size_t hex_length = strlen(message_hex);
            if ((hex_length & 1U) != 0 ||
                hex_length / 2 > maximum_message ||
                !parse_hex(fixture[lane].message, hex_length / 2,
                           message_hex)) {
                fclose(file);
                return 0;
            }
            fixture[lane].message_length = hex_length / 2;
        }
        seen |= (uint8_t)(UINT8_C(1) << lane);
    }
    fclose(file);
    return seen == 0xff;
}

static uint64_t
nanoseconds(void)
{
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &now) != 0)
        abort();
    return (uint64_t)now.tv_sec * UINT64_C(1000000000) +
           (uint64_t)now.tv_nsec;
}

int
main(int argc, char **argv)
{
    if (argc != 4) {
        fprintf(stderr, "usage: %s FIXTURE ITERATIONS SAMPLES\n", argv[0]);
        return 2;
    }
    const size_t iterations = (size_t)strtoull(argv[2], NULL, 10);
    const size_t samples = (size_t)strtoull(argv[3], NULL, 10);
    if (iterations == 0 || samples == 0 || !narya_r51x8_available())
        return 2;

    verify_fixture fixture[lanes] = {0};
    if (!load_fixture(argv[1], fixture))
        return 2;

    uint8_t public_key[lanes * 32];
    uint8_t signature[lanes * 64];
    const uint8_t *message[lanes];
    size_t length[lanes];
    for (size_t lane = 0; lane < lanes; lane++) {
        memcpy(&public_key[lane * 32], fixture[lane].public_key, 32);
        memcpy(&signature[lane * 64], fixture[lane].signature, 64);
        message[lane] = fixture[lane].message;
        length[lane] = fixture[lane].message_length;
    }

    const size_t workspace_size =
        narya_ed25519_verify_strict_x8_workspace_size();
    void *workspace = malloc(workspace_size);
    if (workspace == NULL)
        return 2;

    volatile unsigned int verdict_sink = 0;
    for (size_t warmup = 0; warmup < 256; warmup++) {
        uint8_t verdict = 0;
        if (narya_ed25519_verify_strict_x8(
                &verdict, public_key, signature, message, length, 0xff,
                workspace, workspace_size) != NARYA_OK ||
            verdict != 0xff)
            return 1;
        verdict_sink += verdict;
    }

    for (size_t sample = 0; sample < samples; sample++) {
        const uint64_t start = nanoseconds();
        for (size_t iteration = 0; iteration < iterations; iteration++) {
            uint8_t verdict = 0;
            if (narya_ed25519_verify_strict_x8(
                    &verdict, public_key, signature, message, length, 0xff,
                    workspace, workspace_size) != NARYA_OK ||
                verdict != 0xff)
                return 1;
            verdict_sink += verdict;
        }
        const uint64_t elapsed = nanoseconds() - start;
        const double ns_group = (double)elapsed / (double)iterations;
        printf("sample=%zu ns/group=%.3f ns/signature=%.3f\n",
               sample + 1, ns_group, ns_group / lanes);
    }

    if (verdict_sink == 0)
        return 1;
    free(workspace);
    return 0;
}
