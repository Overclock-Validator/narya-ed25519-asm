CC ?= cc
CLANG ?= clang
AR ?= ar
LAKE ?= lake
CFLAGS ?= -O3 -g -std=c11 -Wall -Wextra -Wpedantic
CPPFLAGS ?= -Iinclude -Isrc

BUILD := build
LIB := $(BUILD)/libnarya_ed25519_asm.a
OBJECTS := \
	$(BUILD)/dispatch.o \
	$(BUILD)/decode_x8.o \
	$(BUILD)/fixed_base_comb.o \
	$(BUILD)/fixed_base_comb_data.o \
	$(BUILD)/affine_niels_transpose_x8.o \
	$(BUILD)/point_x8.o \
	$(BUILD)/projective_niels_table.o \
	$(BUILD)/projective_niels_transpose_x8.o \
	$(BUILD)/r51x8.o \
	$(BUILD)/r51x8_ifma.o \
	$(BUILD)/scalar_reduce.o \
	$(BUILD)/scalar_reduce_x8.o \
	$(BUILD)/scalar_recode.o \
	$(BUILD)/scalar_mult_x8.o \
	$(BUILD)/sha512x8.o \
	$(BUILD)/sha512x8_asm.o \
	$(BUILD)/verify_strict_x8.o

.PHONY: all clean test test-native test-sanitize fuzz-build check check-source check-r51-mul-trace test-r51-mul-trace-mutations check-transpose check-scalar-bounds check-sha512-schedule check-generated formal-check

all: $(LIB)

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/dispatch.o: src/dispatch.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/r51x8.o: src/r51x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/point_x8.o: src/point_x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/projective_niels_table.o: src/projective_niels_table.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/decode_x8.o: src/decode_x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/fixed_base_comb.o: src/fixed_base_comb.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/fixed_base_comb_data.o: src/fixed_base_comb_data.S data/narya_fixed_base_comb_r256.bin | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(BUILD)/affine_niels_transpose_x8.o: src/affine_niels_transpose_x8.S | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(BUILD)/sha512x8.o: src/sha512x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/scalar_reduce.o: src/scalar_reduce.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/scalar_recode.o: src/scalar_recode.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/scalar_mult_x8.o: src/scalar_mult_x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/verify_strict_x8.o: src/verify_strict_x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/r51x8_ifma.o: src/r51x8_ifma.S | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(BUILD)/sha512x8_asm.o: src/sha512x8.S | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(BUILD)/scalar_reduce_x8.o: src/scalar_reduce_x8.S | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(BUILD)/projective_niels_transpose_x8.o: src/projective_niels_transpose_x8.S | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(LIB): $(OBJECTS)
	$(AR) rcs $@ $(OBJECTS)

$(BUILD)/test_r51x8: tests/test_r51x8.c $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_decode_vectors: tests/test_decode_vectors.c tests/reference_r51x8.h $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_sha512x8: tests/test_sha512x8.c $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_scalar_reduce: tests/test_scalar_reduce.c $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_scalar_recode: tests/test_scalar_recode.c $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_projective_niels_table: tests/test_projective_niels_table.c tests/vectors/narya_basepoint_multiples_v1.txt $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_scalar_mult_x8: tests/test_scalar_mult_x8.c tests/vectors/narya_basepoint_multiples_v1.txt tests/vectors/narya_variable_scalar_mult_v1.txt $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_verify_strict_x8: tests/test_verify_strict_x8.c tests/vectors/narya_strict_verify_v1.txt $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_fixed_base_comb: tests/test_fixed_base_comb.c tests/vectors/narya_fixed_base_scalar_v1.txt $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

$(BUILD)/test_external_vectors: tests/test_external_vectors.c tests/vectors/narya_external_strict_v1.jsonl $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

test: $(BUILD)/test_r51x8 $(BUILD)/test_decode_vectors $(BUILD)/test_sha512x8 $(BUILD)/test_scalar_reduce $(BUILD)/test_scalar_recode $(BUILD)/test_projective_niels_table $(BUILD)/test_scalar_mult_x8 $(BUILD)/test_fixed_base_comb $(BUILD)/test_verify_strict_x8 $(BUILD)/test_external_vectors
	$(BUILD)/test_r51x8
	$(BUILD)/test_decode_vectors tests/vectors/narya_permissive_decode_v1.txt
	$(BUILD)/test_sha512x8
	$(BUILD)/test_scalar_reduce
	$(BUILD)/test_scalar_recode
	$(BUILD)/test_projective_niels_table tests/vectors/narya_basepoint_multiples_v1.txt
	$(BUILD)/test_scalar_mult_x8 tests/vectors/narya_basepoint_multiples_v1.txt tests/vectors/narya_variable_scalar_mult_v1.txt
	$(BUILD)/test_fixed_base_comb tests/vectors/narya_fixed_base_scalar_v1.txt
	$(BUILD)/test_verify_strict_x8 tests/vectors/narya_strict_verify_v1.txt
	$(BUILD)/test_external_vectors tests/vectors/narya_external_strict_v1.jsonl

test-native: $(BUILD)/test_r51x8 $(BUILD)/test_decode_vectors $(BUILD)/test_sha512x8 $(BUILD)/test_scalar_reduce $(BUILD)/test_scalar_recode $(BUILD)/test_projective_niels_table $(BUILD)/test_scalar_mult_x8 $(BUILD)/test_fixed_base_comb $(BUILD)/test_verify_strict_x8 $(BUILD)/test_external_vectors
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_r51x8
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_decode_vectors tests/vectors/narya_permissive_decode_v1.txt
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_sha512x8
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_scalar_reduce
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_scalar_recode
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_projective_niels_table tests/vectors/narya_basepoint_multiples_v1.txt
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_scalar_mult_x8 tests/vectors/narya_basepoint_multiples_v1.txt tests/vectors/narya_variable_scalar_mult_v1.txt
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_fixed_base_comb tests/vectors/narya_fixed_base_scalar_v1.txt
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_verify_strict_x8 tests/vectors/narya_strict_verify_v1.txt
	NARYA_REQUIRE_IFMA=1 $(BUILD)/test_external_vectors tests/vectors/narya_external_strict_v1.jsonl

test-sanitize:
	$(MAKE) clean
	$(MAKE) CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -fno-omit-frame-pointer -fsanitize=address,undefined' test-native

fuzz-build:
	$(MAKE) clean
	$(MAKE) CC=$(CLANG) CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -fno-omit-frame-pointer -fsanitize=address,undefined' $(LIB)
	$(CLANG) $(CPPFLAGS) -O1 -g -std=c11 -Wall -Wextra -Wpedantic \
		-fno-omit-frame-pointer -fsanitize=fuzzer,address,undefined \
		tests/fuzz_verify_strict_x8.c $(LIB) -o $(BUILD)/fuzz_verify_strict_x8

check: check-source check-generated formal-check
	$(MAKE) clean
	$(MAKE) CFLAGS='-O2 -g -std=c11 -Wall -Wextra -Wpedantic -Werror' test-native

# This target is useful on non-x86 development hosts. It checks the standalone
# assembly parser without trying to link or execute the resulting ELF object.
check-source:
	$(CLANG) --target=x86_64-unknown-linux-gnu -c src/r51x8_ifma.S -o /tmp/narya-r51x8-ifma.o
	$(CLANG) --target=x86_64-unknown-linux-gnu -c src/sha512x8.S -o /tmp/narya-sha512x8.o
	$(CLANG) --target=x86_64-unknown-linux-gnu -c src/scalar_reduce_x8.S -o /tmp/narya-scalar-reduce-x8.o
	$(CLANG) --target=x86_64-unknown-linux-gnu -c src/projective_niels_transpose_x8.S -o /tmp/narya-projective-niels-transpose-x8.o
	$(CLANG) --target=x86_64-unknown-linux-gnu -c src/affine_niels_transpose_x8.S -o /tmp/narya-affine-niels-transpose-x8.o
	$(CLANG) --target=x86_64-unknown-linux-gnu -c src/fixed_base_comb_data.S -o /tmp/narya-fixed-base-comb-data.o
	$(MAKE) check-r51-mul-trace
	$(MAKE) test-r51-mul-trace-mutations
	$(MAKE) check-transpose
	$(MAKE) check-scalar-bounds
	$(MAKE) check-sha512-schedule

check-r51-mul-trace:
	python3 tools/generate_r51_mul_trace.py --check

test-r51-mul-trace-mutations:
	python3 tools/test_r51_mul_trace_mutations.py

check-transpose:
	python3 tools/check_transpose_schedule.py

check-scalar-bounds:
	python3 tools/check_scalar_reduce_bounds.py

check-sha512-schedule:
	python3 tools/check_sha512_schedule.py

check-generated:
	python3 tools/check_generated.py

formal-check: check-r51-mul-trace
	@if grep -R -n -E '\b(sorry|admit|axiom)\b' formal/lean \
		--include='*.lean' --exclude-dir='.lake'; then \
		echo 'untrusted Lean placeholder or custom axiom found' >&2; exit 1; \
	fi
	cd formal/lean && $(LAKE) build

clean:
	rm -rf $(BUILD)
