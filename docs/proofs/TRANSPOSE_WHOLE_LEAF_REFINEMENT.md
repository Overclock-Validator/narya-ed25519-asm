# Whole-leaf binary refinement for Niels transpose selectors

This certificate covers the exact relocation-free ET_REL symbols:

```text
narya_projective_niels_transpose_x8_asm
narya_affine_niels_transpose_x8_asm
```

It extends the previously checked eight-instruction shuffle blocks to the
complete System V leaves, stated over the byte-addressed machine model in
`X86Machine.lean`. The two transpose sources are unchanged since commit
`571f224057b11faa1f0fd968d6d282d515a4a7bf`; the symbol hashes below identify
the proved bytes.

## Theorem

`projective_whole_leaf_binary_refines` and `affine_whole_leaf_binary_refines`
in `TransposeX86WholeSoundness.lean` have the same shape. For every entry
machine state that satisfies the leaf contract:

1. the committed symbol bytes decode to the source-generated instruction list;
2. running that instruction list returns normally, with no fault;
3. for every coordinate, limb, and lane, the output qword equals the entry
   memory qword of the source selected for that lane:

   ```text
   projective  out[320*coordinate + 64*limb + 8*lane]
                 = source[lane][32*limb + 8*coordinate]     coordinate < 4

   affine      out[320*coordinate + 64*limb + 8*lane]
                 = source[lane][24*limb + 8*coordinate]     coordinate < 3
   ```

   where `source[lane]` is the pointer stored in slot `lane` of the table
   passed in `RSI`, and `out` is the pointer passed in `RDI`;
4. no byte outside the output object (1280 bytes projective, 960 bytes affine)
   changes, and page permissions are unchanged;
5. `RSP` advances by eight, `RIP` is the entry return word, `RAX` holds the
   output pointer, and `RBX`, `RBP`, `R12` to `R15`, `RFLAGS`, `MXCSR`, and
   unmodeled state are preserved.

The lane maps in item 3 cover every aligned qword of the output object, so
items 3 and 4 together determine the entire final memory.

### Leaf contract

`LeafPre` plus the two return-slot premises require exactly:

- the 64-byte pointer table at `RSI` is readable;
- each of the eight source objects is readable for its exact length (160 bytes
  projective, 120 bytes affine);
- the output object at `RDI` is writable for its exact length;
- the output object does not overlap the pointer table, any source object, or
  the eight-byte return slot at `RSP`;
- the return slot is readable.

Source objects may overlap one another and the pointer table. No premise
mentions any byte outside these regions. `leaf_contract_satisfiable` exhibits a
concrete entry state that meets every premise, so the theorems are not vacuous.

### Affine guard-page boundary

An affine source is exactly 120 bytes, and the contract grants read permission
to exactly those 120 bytes. The last row is loaded with EVEX.256
`VMOVDQU64 {k1}{z}` and `K1 = 0b0111`. The machine model checks permission
qword by qword and only for enabled mask bits, so the masked-off qword at source
offset 120 is never consulted. The theorem therefore covers a source that ends
immediately before an unreadable page.

This is fail-closed in both directions:

- `affine_unmasked_tail_load_rejected`: an unmasked 32-byte load of the last
  row is rejected by the symbolic executor;
- `masked_load_with_unknown_opmask_rejected`: a masked load is rejected unless
  the opmask register was set from a known constant earlier in the program.

A native regression also places each 120-byte source immediately before a
`PROT_NONE` page and executes the leaf on supported hardware.

## Proof structure

The proof is reflective. It has three parts with separate review surfaces.

1. **Decoder** (`TransposeX86WholeDecoder.lean`). A restricted decoder consumes
   the exact committed symbol bytes and must produce the instruction list that
   `tools/generate_transpose_whole_trace.py` extracts independently from the
   assembly source. Covered forms: 64-bit register move, pointer-table load,
   `mov eax, imm32`, `kmovb`, VEX/EVEX YMM load, masked zeroing YMM load, YMM
   store, the three shuffle instructions, `VZEROUPPER`, and `RET`.

2. **Symbolic execution** (`TransposeX86WholeLeaf.lean`). A value-parametric
   executor runs the non-returning body with opaque tokens for source qwords.
   Because the values are opaque, the lane maps cannot hold by arithmetic
   coincidence. The executor is partial and returns `none` whenever it cannot
   justify an instruction: unknown base pointer, unknown opmask, out-of-bounds
   source access, misaligned or out-of-bounds store, or `RET`. Kernel evaluation
   (`decide`) shows it accepts both bodies and yields the lane maps.

3. **Soundness** (`TransposeX86WholeSoundness.lean`). `executeSym_sound` proves,
   once for every instruction form, that an accepted symbolic step is matched
   by a fault-free concrete step that preserves a simulation relation: GPRs,
   the low 256 bits of every vector register, known opmasks, permissions, the
   frame outside the output object, and every stored output qword.
   `runSym_sound` lifts this to whole bodies, and `run_body_then_epilogue`
   composes the exact `VZEROUPPER; RET` suffix.

The soundness theorem does not mention either program. A future leaf in the
same instruction subset needs a decoder check and kernel evaluation of the
symbolic executor, not a new machine proof.

The symbolic access log (`projective_exact_source_read_set`,
`affine_exact_source_read_set`, `affine_masked_tail_not_read`) records which
source qwords the symbolic executor requested. It is supplementary. The
machine-level statement of the same property is that the leaf cannot fault
under the exact-length read permissions above.

## Exact artifacts

```text
projective symbol size:   1021 bytes
projective SHA-256:       bfd18091297a1f37647824ca2a7117441df2d21129d6eda5b32fb250fe5ab17d
projective instructions:  171

affine symbol size:       1058 bytes
affine SHA-256:           4acfb4850a09e173635a13b5e242beb1aa2344e10487f4e1968e79c0f4b35f91
affine instructions:      163
```

Any executable-section relocation is rejected.

## Fail-closed gates

Source extraction and object decoding are independent. Mutation tests require
rejection of changes to:

- symbol extents, executable-section relocations, pointer assignments, and
  pointer-table offsets;
- affine mask immediate, mask register, EVEX mask field, and zeroing bit;
- source-load offsets, including the guard-page tail;
- output-store offsets;
- shuffle immediates;
- `VZEROUPPER` or `RET`.

Run:

```sh
make check-transpose-whole-trace
make check-transpose-whole-object
make test-transpose-whole-trace-mutations
make test-transpose-whole-object-mutations
make test-transpose-whole-native
make formal-check
```

## Trusted and unproved boundary

The certificate is relative to:

- the restricted x86 decoder and the instruction semantics in
  `TransposeX86WholeInstruction.lean` and `X86Machine.lean`, which are
  definitions and must be reviewed against the architecture manuals;
- Lean, mathlib, and the Lean kernel. The qword store/load read-back lemma
  inherited from `X86Machine.lean` uses `bv_decide`, so the capstones also
  depend on `Lean.ofReduceBool`, as the r51 multiplier theorem already does;
- the source and object extraction scripts and the selected compiler
  invocation.

It does **not** prove:

- that a downstream application contains these exact symbols unless that binary
  is checked separately;
- compiler, assembler, linker, loader, kernel, microcode, or physical-CPU
  correctness;
- absence of speculative or other unobservable microarchitectural reads;
- public dispatch, CPUID, or XCR0 correctness;
- behaviour when the output object overlaps a source, the pointer table, or the
  return slot, which the leaf contract forbids;
- that the C callers of the two selectors establish the leaf contract;
- correctness of any cryptographic arithmetic beyond this representation-only
  transpose.

The native guard-page test is physical evidence, not part of the formal proof
and not a substitute for review of the architectural semantics.
