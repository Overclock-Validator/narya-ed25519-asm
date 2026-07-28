# r51 multiply assembly-source refinement

This certificate connects the checked GNU assembly **source** for
`narya_r51x8_mul_ifma` to the Lean arithmetic theorem. It closes the previous
hand-maintained source/model mirror. It does not decode the emitted ELF object
or constitute a complete x86 proof.

## Checked chain

```text
src/r51x8_ifma.S
        |
        | fail-closed extraction
        v
GeneratedR51MulTrace.lean
        |
        | generated schedule equalities + arithmetic/range proofs
        v
radix51_mul_assembly_trace_correct
```

[`tools/generate_r51_mul_trace.py`](../../tools/generate_r51_mul_trace.py)
accepts only the straight-line multiply leaf and macro bodies modeled by the
proof. It emits
[`GeneratedR51MulTrace.lean`](../../formal/lean/NaryaFormal/GeneratedR51MulTrace.lean).
[`AssemblyTrace.lean`](../../formal/lean/NaryaFormal/AssemblyTrace.lean)
imports those generated definitions. Its final theorem is stated over
`assemblyOutput`, the output expression extracted from the source stores.

An edit to the assembly can have three valid outcomes:

1. extraction rejects an unmodeled source shape;
2. the generated Lean artifact changes and the reproducibility gate fails;
3. after intentional regeneration, Lean accepts the changed trace only if the
   source-derived output still satisfies the product, no-wrap, and u52-output
   theorems.

Merely updating a comment or a separately mirrored model cannot make a changed
kernel pass.

## Source facts extracted

The extractor checks or records:

- exact `CLEAR`, `MUL_PAIR`, `COMBINE_HIGH`, `FOLD_INTO`, and `NORMALIZE_5`
  macro bodies;
- all ten source loads, their limb offsets, and their position before
  arithmetic and output stores;
- the ordered 25 `MUL_PAIR` calls, input-limb identities, low/high accumulator
  targets, and completeness of the 5x5 product set;
- every high-half rebase, degree-9 shift, modular-fold source/destination, and
  the fold and mask constants;
- normalization input/carry registers and output-store mapping; and
- the leaf epilogue and absence of any unrecognized instruction or directive.

The allowed instructions are lane-wise. The source check therefore excludes a
shuffle or horizontal operation from this leaf. The Lean theorem proves one
scalar lane, which applies pointwise to all eight source lanes under the
documented instruction semantics.

## Mutation evidence

[`tools/test_r51_mul_trace_mutations.py`](../../tools/test_r51_mul_trace_mutations.py)
changes one representative fact in each major class and requires rejection:

- accumulator clearing and IFMA opcode;
- product presence and accumulator target;
- high-half combine and fold source;
- fold constant and normalize operand order;
- source-load offset and output-store lane mapping; and
- insertion of an otherwise unmodeled arithmetic instruction.

These tests establish that the extraction gate has teeth. They are not a
substitute for reviewing the extractor itself.

## Reproduce

From the repository root:

```sh
make check-r51-mul-trace
make test-r51-mul-trace-mutations
make formal-check
```

`make formal-check` depends on the source-trace equality check. Consequently,
changing `src/r51x8_ifma.S` without updating its generated proof input makes
the formal gate fail.

## Remaining trust boundary

The first object-code link is now closed for the canonical proof ELF:

```text
exact 800 linked bytes -> restricted decoder -> 129 source instructions
```

`X86ObjectRefinement.lean` kernel-checks that equality. The decoder rejects
unmodeled maps, opcodes, masks, vector widths, ModRM modes, and displacement
forms; it is not a general x86 decoder. The next open link is execution:

```text
decoded instruction trace -> BitVec/memory execution -> scalar source trace
```

The present certificate still trusts the ELF extractor and source parser. It
does not yet prove the complete System V call/return and memory-frame theorem,
CPUID/XCR0 dispatch, or that a downstream executable contains the canonical
proof ELF's bytes. Native exact-output, alias, and lane differentials remain
independent evidence for those boundaries.
