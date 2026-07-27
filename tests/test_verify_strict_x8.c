/* Copyright 2026 Overclock Validator; SPDX-License-Identifier: Apache-2.0 */
#include "narya_ed25519_asm.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { lanes = 8, maximum_message = 4096 };

typedef struct verify_fixture {
    uint8_t public_key[32];
    uint8_t signature[64];
    uint8_t message[maximum_message];
    size_t message_length;
} verify_fixture;

static const uint8_t scalar_order[32] = {
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
};

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
            lane >= lanes || !parse_hex(fixture[lane].public_key, 32, public_hex) ||
            !parse_hex(fixture[lane].signature, 64, signature_hex)) {
            fclose(file);
            return 0;
        }
        if (strcmp(message_hex, "-") == 0) {
            fixture[lane].message_length = 0;
        } else {
            const size_t hex_length = strlen(message_hex);
            if ((hex_length & 1U) != 0 || hex_length / 2 > maximum_message ||
                !parse_hex(fixture[lane].message, hex_length / 2, message_hex)) {
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

static void
marshal(
    uint8_t public_key[lanes * 32],
    uint8_t signature[lanes * 64],
    const uint8_t *message[lanes],
    size_t length[lanes],
    const verify_fixture fixture[lanes])
{
    for (size_t lane = 0; lane < lanes; lane++) {
        memcpy(&public_key[lane * 32], fixture[lane].public_key, 32);
        memcpy(&signature[lane * 64], fixture[lane].signature, 64);
        message[lane] = fixture[lane].message;
        length[lane] = fixture[lane].message_length;
    }
}

static int
verify(
    uint8_t *verdict,
    const uint8_t public_key[lanes * 32],
    const uint8_t signature[lanes * 64],
    const uint8_t *const message[lanes],
    const size_t length[lanes],
    uint8_t active,
    void *workspace,
    size_t workspace_size)
{
    return narya_ed25519_verify_strict_x8(
        verdict, public_key, signature, message, length, active,
        workspace, workspace_size) == NARYA_OK;
}

int
main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s VERIFY_FIXTURE\n", argv[0]);
        return 1;
    }
    const char *required = getenv("NARYA_REQUIRE_IFMA");
    if (!narya_r51x8_available()) {
        if (required != NULL && required[0] == '1') {
            fputs("AVX-512 IFMA required but unavailable\n", stderr);
            return 1;
        }
        puts("SKIP: AVX-512 IFMA unavailable");
        return 0;
    }

    verify_fixture fixture[lanes] = {0};
    if (!load_fixture(argv[1], fixture)) {
        fputs("failed to load strict-verification fixture\n", stderr);
        return 1;
    }

    const size_t workspace_size = narya_ed25519_verify_strict_x8_workspace_size();
    void *workspace = malloc(workspace_size);
    if (workspace == NULL)
        return 1;
    if ((uintptr_t)workspace % narya_ed25519_verify_strict_x8_workspace_alignment() != 0) {
        fputs("malloc did not satisfy verifier workspace alignment\n", stderr);
        free(workspace);
        return 1;
    }

    uint8_t public_key[lanes * 32], signature[lanes * 64];
    const uint8_t *message[lanes];
    size_t length[lanes];
    marshal(public_key, signature, message, length, fixture);

    uint8_t verdict = 0;
    if (!verify(&verdict, public_key, signature, message, length, 0xff,
                workspace, workspace_size) || verdict != 0xff) {
        fprintf(stderr, "valid strict fixture verdict=%02x\n", verdict);
        free(workspace);
        return 1;
    }

    /* Every subset must preserve both lane identity and vacuous inactivity. */
    for (unsigned int active = 0; active <= 0xff; active++) {
        verdict = 0;
        if (!verify(&verdict, public_key, signature, message, length,
                    (uint8_t)active, workspace, workspace_size) ||
            verdict != (uint8_t)active) {
            fprintf(stderr, "active-mask strict verdict=%02x want=%02x\n",
                    verdict, active);
            free(workspace);
            return 1;
        }
    }

    /* A late equation failure in one message must not disturb neighbours. */
    for (size_t bad = 0; bad < lanes; bad++) {
        uint8_t changed[maximum_message] = {0};
        memcpy(changed, fixture[bad].message, fixture[bad].message_length);
        size_t changed_length = fixture[bad].message_length;
        if (changed_length == 0)
            changed_length = 1;
        changed[0] ^= 1;
        const uint8_t *saved = message[bad];
        const size_t saved_length = length[bad];
        message[bad] = changed;
        length[bad] = changed_length;
        verdict = 0;
        if (!verify(&verdict, public_key, signature, message, length, 0xff,
                    workspace, workspace_size) ||
            verdict != (uint8_t)(0xffU ^ (UINT8_C(1) << bad))) {
            fprintf(stderr, "late invalid lane=%zu verdict=%02x\n", bad, verdict);
            free(workspace);
            return 1;
        }
        message[bad] = saved;
        length[bad] = saved_length;
    }

    /* Canonical-S and pure-small-order A/R gates are lane local. */
    for (size_t bad = 0; bad < lanes; bad++) {
        uint8_t saved_s[32], saved_a[32], saved_r[32];
        memcpy(saved_s, &signature[bad * 64 + 32], 32);
        memcpy(&signature[bad * 64 + 32], scalar_order, 32);
        verdict = 0;
        if (!verify(&verdict, public_key, signature, message, length, 0xff,
                    workspace, workspace_size) ||
            verdict != (uint8_t)(0xffU ^ (UINT8_C(1) << bad))) {
            fprintf(stderr, "noncanonical S lane=%zu verdict=%02x\n", bad, verdict);
            free(workspace);
            return 1;
        }
        memcpy(&signature[bad * 64 + 32], saved_s, 32);

        memcpy(saved_a, &public_key[bad * 32], 32);
        memset(&public_key[bad * 32], 0, 32);
        public_key[bad * 32] = 1;
        verdict = 0;
        if (!verify(&verdict, public_key, signature, message, length, 0xff,
                    workspace, workspace_size) ||
            verdict != (uint8_t)(0xffU ^ (UINT8_C(1) << bad))) {
            fprintf(stderr, "small-order A lane=%zu verdict=%02x\n", bad, verdict);
            free(workspace);
            return 1;
        }
        memcpy(&public_key[bad * 32], saved_a, 32);

        memcpy(saved_r, &signature[bad * 64], 32);
        memset(&signature[bad * 64], 0, 32);
        signature[bad * 64] = 1;
        verdict = 0;
        if (!verify(&verdict, public_key, signature, message, length, 0xff,
                    workspace, workspace_size) ||
            verdict != (uint8_t)(0xffU ^ (UINT8_C(1) << bad))) {
            fprintf(stderr, "small-order R lane=%zu verdict=%02x\n", bad, verdict);
            free(workspace);
            return 1;
        }
        memcpy(&signature[bad * 64], saved_r, 32);
    }

    /* API errors preserve the caller's verdict byte. */
    verdict = 0xa5;
    if (narya_ed25519_verify_strict_x8(
            &verdict, public_key, signature, message, length, 0xff,
            workspace, workspace_size - 1) != NARYA_ERR_INVALID_ARGUMENT ||
        verdict != 0xa5) {
        fputs("workspace error was not output-atomic\n", stderr);
        free(workspace);
        return 1;
    }

    free(workspace);
    puts("PASS: complete x8 DalekStrict equation matches independent signatures");
    return 0;
}
