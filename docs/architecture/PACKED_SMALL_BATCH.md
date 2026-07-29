# Coordinate-packed small-batch verifier

## Purpose and dispatch boundary

The public batch API routes counts one and two through a coordinate-packed
verifier. Counts three through 64 retain the signature-parallel x8 path. The
choice changes scheduling only: both paths enforce the same `DalekStrict`
predicate and return one independent verdict bit per input.

This route exists because padding a singleton into a signature-parallel x8
group performs almost the cost of eight signatures for one verdict. In the
packed representation, the four extended Edwards coordinates of one point
fill four SIMD lanes. On a native-512 machine, two independent points fill one
ZMM register:

```text
lanes 0..3 = signature 0 [X,Y,T,Z]
lanes 4..7 = signature 1 [X,Y,T,Z]
```

An n=1 call uses the low half and initializes the high half to the identity.
There is no horizontal arithmetic: permutations repeat independently in both
256-bit halves, and field multiplication remains lane-wise.

## Verification schedule

For each live signature `(R,S)` and public key `A`:

1. Apply the strict byte prechecks: canonical `S`, non-small-order `A` and
   `R`, and canonical `R`.
2. Hash the original bytes `SHA512(R || A || M)`. Counts one and two use the
   scalar FIPS-180-4 implementation because constructing an eight-lane message
   schedule dominated a partially occupied group. Wider groups retain the x8
   assembly compressor.
3. Reduce the digest modulo `l` to obtain `k`.
4. Decode each `(A,R)` pair together in adjacent decoder lanes. This shares
   one square-root schedule without changing either decoded point.
5. Build the eight positive odd multiples `[1,3,...,15]A` needed by width-5
   NAF.
6. Evaluate `Q = [S]B - [k]A` on one shared doubling chain. `-k` uses exact
   signed-integer width-5 NAF; `S` uses exact signed-integer width-8 NAF.
7. Compare `Q` with the decoded `R` projectively using
   `X_Q = x_R Z_Q` and `Y_Q = y_R Z_Q`. This needs no inversion. Canonical-R
   was already established from the original bytes.

The immutable generator table contains affine cached encodings of the 64
positive odd multiples `[1,3,...,127]B`. It is generated independently by
`tools/generate_packed_naf_basepoint.py`; `make check-generated` pins the
payload. No public-key state survives a call, so this remains a cold verifier.

## Point formulas and assembly boundary

The direct-XY doubling starts with four lane-wise products:

```text
A = X^2, B = Y^2, C = Z^2, D = XY
E = 2D
G = B - A
F = G - 2C
H = -(A + B)
(X',Y',T',Z') = (EF, GH, EH, FG)
```

Cached addition multiplies `[Y-X,Y+X,T,Z]` by cached
`[Y-X,Y+X,2dT,2Z]`, derives the standard `[E,G,H,F]` linear layer, and uses
the same four final packed products.

`src/packed_x4_ifma.S` fuses each operand permutation with the existing
25-product radix-51 multiplication schedule. The convolution, high-half
reconstruction, `B^5 = 19` fold, and final carry are intentionally identical
to `narya_r51x8_mul_ifma`; only operand production is kept in registers. The
split leaves remain available as direct test oracles. Native tests assert
bit-for-bit equality between every fused and split form for maximum-u52 and
heterogeneous random inputs, including supported aliases.

The implementation is a System V translation of Narya's Go packed verifier
and two-chain experiment at source commit
`1354f6001609c60b5a67b7b5b4af08d391c4c468`. The standalone implementation
adds fused first/final multiplication leaves and independently regenerates its
fixed generator payload.

## Exactness and range boundary

- Every field multiplication input is composable-u52.
- Linear layers use explicit multiples of `p` before unsigned subtraction.
- One parallel carry/fold returns every result to the composable-u52 domain.
- All source vectors are loaded before the first output store at each claimed
  alias-safe boundary.
- Inactive halves are the extended identity and cached identity, never zeros
  interpreted as a point.
- A failed precheck, decode, reduction, or scalar recode clears only that
  signature's live bit. No invalid lane can cancel a valid equation.

The direct native suite executes all 2,954 committed RFC/CCTV/Wycheproof and
boundary cases as singletons, every adjacent pair as n=2, and the original
wide-batch oracle. This is strong differential evidence, not a universal
proof.

## Open formal obligations

The existing byte-linked Lean theorem covers the character-identical standalone
field-multiply leaf, not the new packed symbols. Before claiming end-to-end
formal coverage, add:

1. a source or object trace proving the `VPERMQ` maps independently implement
   the two `[X,Y,T,Z]` halves;
2. interval/no-wrap proofs for the packed doubling and cached-add linear maps
   and their exact bias vectors;
3. refinement from the four fused product schedules to the proved r51
   multiplication result;
4. abstract Edwards proofs for the doubling, cached addition, NAF table, and
   shared-chain equation;
5. a wrapper theorem for scalar SHA-512 padding, scalar reduction lane
   placement, `(A,R)` decoder placement, and verdict-bit routing; and
6. deployed-object identity and physical-CPU correctness, which remain outside
   the current Lean model.

## Performance evidence

The dated raw evidence is under
`docs/reproducibility/zen5-packed-small-2026-07-29`. Results there are for one
pinned Zen 5 core and are not a Zen 4 or cross-machine claim.
