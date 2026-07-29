# x8 Niels-addition schedule

This document describes the bounded assembly boundary used by both the
variable-base projective-Niels addition and the fixed-base affine-Niels
addition. The exact interval argument is in
[`R51_FIELD_CONTRACT.md`](../proofs/R51_FIELD_CONTRACT.md).

## Formula

For a complete extended point `(X,Y,Z,T)` and a cached projective-Niels point
`(Yc+Xc,Yc-Xc,Zc,2dTc)`, Narya computes:

```text
A = (Y-X)(Yc-Xc)       B = (Y+X)(Yc+Xc)
C = T(2dTc)            D = ZZc
E = B-A                F = 2D-C
G = 2D+C               H = B+A

X' = EF   Y' = GH   Z' = FG   T' = EH.
```

For an affine-Niels cached point, `Zc=1`; `D` is the carried point `Z` and the
fourth input multiplication disappears.

The C wrapper first computes normalized `Y-X` and `Y+X`. The projective leaf
then forms four exact folded raw products; the affine leaf forms three and
copies `Z`. One fused linear layer applies a `535p` unsigned-subtraction bias
to `E` and `F`, followed by one parallel carry per `E,F,G,H` output. The four
final coordinate products remain ordinary reviewed field leaves.

This split is intentional. It removes six or seven field-leaf calls and their
redundant carry boundaries without turning an entire addition or scalar round
into one opaque symbol. Formula inputs, normalized linear outputs, and final
products remain independently testable and visible to profilers.

## ABI and aliasing

- Both native leaves use the System V AMD64 ABI and a dedicated 1,280-byte
  four-slot workspace.
- On entry, slots 0 and 1 contain normalized point-side `Y-X` and `Y+X`.
- The workspace must not overlap either point input or cached input.
- Each same-slot raw product loads all ten source vectors before overwriting
  its workspace slot.
- The C point wrapper supports exact `out == point`: every point coordinate is
  consumed by Stage 2 before final-product stores begin.
- `out` must not overlap the cached table record.
- All vector arithmetic is lane-wise; no instruction moves data between
  signature lanes.

## Validation

The native field/point gate calls both Stage-2 leaves directly with
maximum-u52 and heterogeneous random coordinates. It independently recomputes
`A..H`, checks every output modulo `p`, and asserts every exit limb is below
`2^52`. Complete table construction, variable/fixed scalar multiplication,
strict verification, 2,954 external vectors, warning-as-error builds, and
ASan/UBSan cover the consumers and alias route.

This is currently source-certified and differentially tested, not a
byte-linked Lean theorem. The precise open refinement target is recorded in
[`FORMALIZATION_BACKLOG.md`](../proofs/FORMALIZATION_BACKLOG.md).
