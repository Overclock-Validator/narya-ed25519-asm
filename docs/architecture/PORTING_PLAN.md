# Standalone assembly port

## Goal

Export the optimized Narya verifier through a stable System V AMD64 C ABI,
with no Go ABI, Go runtime, or cgo dependency. The supported first verifier is
the cold, eight-lane, AVX-512 IFMA implementation of the exact `DalekStrict`
predicate. Eight lanes return eight verdicts; this is not randomized aggregate
batch verification.

## Why the port is staged

The Go implementation deliberately separates public policy from private
native preparation records. Replacing the Go call convention mechanically
would preserve instruction syntax but not provide a reviewable external ABI.
The standalone port therefore proceeds by proof boundary:

1. r51×8 field arithmetic, with a scalar independent oracle;
2. Edwards extended/projective-Niels point operations;
3. permissive A/R decompression and strict byte prechecks;
4. SHA-512 and reduction modulo the scalar order;
5. scalar recoding, table construction, and Straus DSM;
6. projective final comparison and independent lane masks;
7. a checked public C wrapper and fault-contained fallback policy.

Each stage must pass bit-exact differential tests before its result may become
an input to the next stage. This keeps a representation error from being
hidden by a later canonical encoding.

## ABI choices

- SysV AMD64 is the first ABI. Windows x64 requires a separate shim because
  its preserved-register and argument rules differ.
- Public structures use fixed-width integers and explicit structure-of-arrays
  layouts. Native leaves use unaligned vector loads, avoiding a hidden caller
  alignment requirement.
- Checked C entry points own feature and input validation. Internal assembly
  leaves are unchecked and may only be called after range proofs establish
  their contracts.
- No public API is exposed for an incomplete verifier. Low-level field entry
  points exist now so the port can be tested independently.

## Source boundary

The initial arithmetic leaf is a syntax/ABI translation of the independently
implemented r51×8 Narya kernel at commit
`eff4c8ddafdfe0448eb50f2eafc723a42b95fe2c`. The distinct r43x6 reference
backend and its Firedancer lineage are not copied into this library.
