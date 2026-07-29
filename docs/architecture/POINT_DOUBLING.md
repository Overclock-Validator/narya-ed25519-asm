# x8 point-doubling schedule

This document describes the promoted cold-path point-doubling boundary. It is
an architecture and audit guide; the exact range certificate is in
[`R51_FIELD_CONTRACT.md`](../proofs/R51_FIELD_CONTRACT.md).

## Formula

For extended Edwards coordinates and `a=-1`, Narya uses the direct-XY form:

```text
A = X^2
B = Y^2
C = Z^2
E = 2XY
G = B - A
F = G - 2C
H = -A - B

X' = E F
Y' = G H
Z' = F G
T' = E H
```

The first four products are independent. The assembly leaf
`narya_r51x8_double_stage2_ifma` expands the reviewed raw multiplier four
times, applies the exact 535/1068/1069 multiples of `p` needed to keep every
subtraction unsigned, and performs one carry layer per `E,F,G,H` output.
The final coordinate products remain ordinary reviewed field leaves.

This split deliberately avoids a monolithic point kernel. An auditor can
review the raw/linear state transition separately from the final products, and
profilers retain visible field-multiplication symbols.

## P3 and P2 states

A complete extended point is represented by the distinct
`narya_edwards_point_x8` type `(X,Y,Z,T)`. A run of dependent doublings uses
`narya_projective_point_x8` `(X,Y,Z)` for intermediate results.

The next doubling reads only `X,Y,Z`, so computing `T'=EH` on every
intermediate result is unnecessary. The radix-32 Horner loop performs:

```text
P3 -> P2 -> P2 -> P2 -> P2 -> P3 -> optional Niels addition
```

for each five-doubling round. The last transition reconstructs `T` before
the point reaches an addition. This is encoded in C types rather than a
runtime “T is stale” flag: no addition function accepts a P2 value, making the
dangerous state unrepresentable at the call boundary.

## Aliasing and memory

- Stage-2 output storage must not overlap `X`, `Y`, or `Z`; the C point
  wrappers allocate a dedicated workspace.
- Each final field multiplication retains its documented exact-alias
  contract.
- P2-to-P2 operation supports exact same-object use because Stage 2 consumes
  all three inputs before final-product stores begin.
- Every AVX-512 instruction remains lane-wise; no shuffle or horizontal
  operation can move one signature's point into another lane.

## Validation

The native point gate independently checks:

- maximum-u52 and heterogeneous random Stage-2 inputs;
- every Stage-2 output limb remains below `2^52`;
- all four outputs equal an independently expressed field schedule modulo
  `p`;
- P3-to-P2, in-place P2-to-P2, and P2-to-P3 transitions against complete
  five-doubling reference chains; and
- complete scalar multiplication, strict verification, and the external
  RFC/CCTV/Wycheproof/boundary corpus.

ASan/UBSan and warning-as-error native builds are part of the dated evidence.
The source-level interval certificate is not an assembled-byte proof; the
remaining Lean/refinement work is listed in
[`FORMALIZATION_BACKLOG.md`](../proofs/FORMALIZATION_BACKLOG.md).

