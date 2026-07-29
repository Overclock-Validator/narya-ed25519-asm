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
4. SHA-512 and reduction modulo the scalar order (implemented as independent
   review seams; fused scheduling remains a performance follow-up);
5. scalar recoding, table construction, and Straus DSM;
6. projective final comparison and independent lane masks;
7. a checked public C wrapper and explicit unsupported-CPU/error policy.

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
- The complete ABI-zero strict verifier and selected low-level review seams are
  public. ABI zero remains intentionally unstable; incomplete experimental
  verifier variants are not exported.

## Source boundary

The initial arithmetic leaf is a syntax/ABI translation of the independently
implemented r51×8 Narya kernel at commit
`eff4c8ddafdfe0448eb50f2eafc723a42b95fe2c`. The distinct r43x6 reference
backend and its Firedancer lineage are not copied into this library.

Later cold-path parity work is ported in reviewable boundaries rather than by
copying the complete Go point loop. The register-resident decoder square and
the raw-product/direct-XY Stage-2, typed P2/P3 doubling schedule, and bounded
projective/affine-Niels Stage-2 leaves correspond to the Go implementation at
`3f7b6885876520f2434e0a89248e106ed144985a`. Each standalone boundary has
its own SysV contract, native differential, dated benchmark, and explicitly
separate formal obligation.

## Current cold-path parity

The standalone verifier now includes:

- the register-resident 15-product decoder square chain;
- four raw doubling products plus the direct-XY linear Stage-2 in one SysV
  leaf; and
- a distinct P2 `(X,Y,Z)` type for four of every five dependent doublings,
  with `T` reconstructed before every Niels addition; and
- fused raw-product and linear/carry Stage-2 leaves for both projective- and
  affine-Niels additions, with final coordinate products kept separate.
- the Go cold verifier's asymmetric fixed-base schedule: 26 balanced
  radix-1024 generator digits are injected into the variable term's existing
  250-doubling radix-32 chain, while the prior radix-256 comb remains an
  independent oracle.

It does not yet include the Go verifier's cross-group compressed-point
finalizer or public batch dispatcher. Those are separate ports, not implied by
field-kernel or scalar-schedule parity.
