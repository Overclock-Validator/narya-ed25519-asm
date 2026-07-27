CC ?= cc
AR ?= ar
CFLAGS ?= -O3 -g -std=c11 -Wall -Wextra -Wpedantic
CPPFLAGS ?= -Iinclude -Isrc

BUILD := build
LIB := $(BUILD)/libnarya_ed25519_asm.a
OBJECTS := \
	$(BUILD)/dispatch.o \
	$(BUILD)/point_x8.o \
	$(BUILD)/r51x8.o \
	$(BUILD)/r51x8_ifma.o

.PHONY: all clean test check-format check-source

all: $(LIB)

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/dispatch.o: src/dispatch.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/r51x8.o: src/r51x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/point_x8.o: src/point_x8.c include/narya_ed25519_asm.h src/internal.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD)/r51x8_ifma.o: src/r51x8_ifma.S | $(BUILD)
	$(CC) $(CPPFLAGS) -c $< -o $@

$(LIB): $(OBJECTS)
	$(AR) rcs $@ $(OBJECTS)

$(BUILD)/test_r51x8: tests/test_r51x8.c $(LIB)
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LIB) -o $@

test: $(BUILD)/test_r51x8
	$(BUILD)/test_r51x8

# This target is useful on non-x86 development hosts. It checks the standalone
# assembly parser without trying to link or execute the resulting ELF object.
check-source:
	$(CC) --target=x86_64-unknown-linux-gnu -c src/r51x8_ifma.S -o /tmp/narya-r51x8-ifma.o

clean:
	rm -rf $(BUILD)
