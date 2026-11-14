# Proof for the multiplier bytes the Go module ships

The production verifier is the Go module `narya-ed25519`. This repository's
`run_r51_multiplier_refines` and `r51_multiplier_reflective` are about an ELF
symbol assembled by Clang from `src/r51x8_ifma.S`. The Go module does not link
that symbol. It has its own Go assembly source, which the Go toolchain
assembles and links. The two builds differ in calling convention, base
registers, constant addresses, and entry prelude, so a theorem about one says
nothing about the bytes of the other.

This note describes the theorem about the Go-linked bytes and the check that a
given binary contains them.

## What is proved

`X86GoR51MulReflective.lean` works on the exact linked bytes of

```text
github.com/Overclock-Validator/narya-ed25519/internal/r51x5.ifmaMulNormalizedUncheckedX8.abi0
```

committed in `GeneratedGoR51ObjectBytes.lean`.

- `symbol_decodes`, `decoded_shape`: the 815 bytes decode completely, in the
  Lean kernel, to three stack-argument loads (`out` from `8(SP)` into RDI, `x`
  from `16(SP)` into RCX, `y` from `24(SP)` into RBX) followed by a
  129-instruction vector program ending in `VZEROUPPER; RET`.
- `checker_accepts`, `output_bounds`: the reflective IFMA checker accepts the
  127 decoded body instructions and bounds every stored limb below `2^52`.
- `go_r51_multiplier_refines`: from any entry state satisfying the Go ABI0
  contract below, the symbol returns normally; the selected lane of the output
  represents the product of the selected-lane inputs modulo `2^255 - 19`;
  every output limb is below `2^52`; no byte outside the 320-byte output
  changes; RSP advances by eight and RIP is the entry return word.
- `go_r51_multiplier_refines_relocated`: the same statement for any two
  distinct constant addresses. This is the form that applies to another
  binary, which links the same code with its constants elsewhere.
- `same_schedule_as_standalone`: the decoded Go vector program is, instruction
  for instruction, the standalone source-generated trace up to the two input
  base registers and the two constant addresses. This is a cross-check. The Go
  theorem does not depend on it and consults no source-level transcript of the
  Go assembly.
- `leaf_contract_satisfiable`: a concrete entry state meets every hypothesis.

### Go ABI0 contract

- The 24 bytes of argument slots at `8(SP)` are readable.
- The ten 64-byte rows of `x` and `y` are readable and their selected lane is
  at most `2^52 - 1`.
- The two linked constants are readable and hold 19 and `2^51 - 1`.
- The 320-byte output object is writable.
- The return slot at `0(SP)` is readable and does not overlap the output.

`x`, `y`, and `out` may overlap arbitrarily, and the argument slots may overlap
the output, because every argument and input load precedes the first store.

## Reference bytes

The committed bytes come from the module's own package test binary, built
twice and required to be byte-identical:

```sh
# in a narya-ed25519 checkout at the pinned commit
GOOS=linux GOARCH=amd64 GOTOOLCHAIN=go1.27.3 go test -c -trimpath \
    -buildvcs=false -ldflags=-buildid= -o r51x5.test ./internal/r51x5
```

```text
module commit       c265ee9667131a556cd332c252b79de0860c7640
toolchain           go1.27.3, linux/amd64
symbol size         815 bytes
symbol SHA-256      5a423a315e174356f39567b3a806dcdc44289f11a2b328946b6c2489cd0af839
normalized SHA-256  bb6f08422eb87d6449e7ba56cbbfe712519f4aea61cc452ecd345488db3b3e1b
```

The normalized hash zeroes the two four-byte displacement fields that address
the constants (symbol offsets 608 and 678). It is the same for every link of
the same code.

```sh
make GO_R51_ELF=/path/to/r51x5.test check-go-r51-object-bytes
```

regenerates the Lean input from that image and requires it to equal the
committed file.

## Checking a binary

```sh
make GO_R51_ELF=/path/to/binary check-go-r51-symbol
```

`tools/check_go_r51_symbol.py` accepts any linked ELF64 x86-64 image and
requires that:

1. the multiplier symbol has the reference length and the reference bytes
   everywhere outside the two displacement fields;
2. each displacement field resolves to a qword in allocated, non-writable,
   non-executable memory;
3. those qwords hold 19 and `2^51 - 1`.

It prints the two constant addresses, which are the `fold19` and `mask51`
arguments of `go_r51_multiplier_refines_relocated` for that image. If the
image has no symbol table, the symbol is found by a byte search that must match
exactly once.

`make GO_R51_ELF=... test-go-r51-symbol-mutations` requires eleven single-point
mutations of a linked image to be rejected: argument slot and register, a
source-load base register, an IFMA opcode, a product source register, a store
displacement, the `RET`, each constant's value, and each displacement target.

### Evidence recorded with this change

- The reference test binary and a stripped (`-s -w`) build of it pass, the
  second by byte search.
- A linux/amd64 Mithril validator binary built with go1.27.3 against the pinned
  module commit passes: 815 bytes, the same normalized SHA-256, constants
  linked at different addresses with the correct values.

## Trusted and unproved boundary

Relative to the standalone proof, this removes the gap between the proved bytes
and the shipped bytes for this one leaf. It remains relative to the Lean kernel
and mathlib, the restricted decoder and instruction semantics, and the small
Python byte extractor. The extractor does not decode: the kernel does.

It does **not** prove:

- that a given binary's decoded program is the reference program with renamed
  addresses. `check_go_r51_symbol.py` establishes byte equality outside the
  displacement fields and that each field resolves to the right constant; the
  step from there to the renamed instruction list rests on the decoder treating
  a displacement uniformly. It can be closed in Lean for a specific image by
  regenerating the Lean input from that image;
- the Go-compiled wrapper `ifmaMultiplyComposableUncheckedX8`, its nil checks,
  its ABIInternal-to-ABI0 argument spill, or its stack-growth path;
- that callers reach this symbol, or CPUID and XCR0 dispatch;
- that callers establish the contract, in particular the `2^52 - 1` input
  bound;
- any other Go-linked leaf: the square chain, point formulas, transposes,
  scalar reduction, and SHA-512 are not covered;
- Go's register conventions around the call. The theorem states what the symbol
  does to machine state; it does not state that this satisfies ABI0;
- the Go assembler and linker, the loader, concurrent memory mutation,
  microcode, or the physical CPU.

A different module commit or Go toolchain can change the bytes. The check then
fails, and the Lean input must be regenerated and the project rebuilt. The
proof text does not mention any byte or address, so it is expected to rebuild
unchanged if the instruction schedule is the same.
