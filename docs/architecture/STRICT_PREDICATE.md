# Strict verification predicate

The public ABI implements eight independent instances of this predicate. Let
`S` be the unsigned little-endian integer represented by all 32 original
`S_bytes`:

```text
require S < l
A, okA = permissive_decode(A_bytes)
R, okR = permissive_decode(R_bytes)
require okA and okR
reject if [8]A = identity
reject if [8]R = identity
require canonical_compressed(R_bytes)
k = SHA512(original_R_bytes || original_A_bytes || message) mod l
Q = [S]B - [k]A
accept iff projective_equal(Q, R)
```

The implementation is free to perform byte-only rejection before decoding.
That evaluation order is an optimization only: every surviving lane must still
successfully decode both `A_bytes` and `R_bytes` before it can be accepted.

This is an equivalent restatement of the pinned
[ed25519-dalek 2.x `verify_strict` source][dalek-verifying]. Dalek performs the
last two requirements together by compressing `Q` and comparing its bytes to
the original signature `R`. Narya establishes canonical `R` before the
equation and then uses two projective cross-products:

```text
field_equal(X_Q * Z_R, X_R * Z_Q)
field_equal(Y_Q * Z_R, Y_R * Z_Q)
```

`field_equal` means equality in `F_p`, not equality of the redundant five-limb
representations. Successful decoding establishes `Z_R != 0`; the point
arithmetic contract must establish that `Q` is a valid projective Edwards point
with `Z_Q != 0`. No field inversion or point serialization is needed at the
final boundary.

The equivalence obligation is explicit: for every successfully decoded
`R_bytes` and valid projective `Q`,

```text
canonical(R_bytes) and projective_equal(Q, Decode(R_bytes))
    iff Encode(Q) == R_bytes.
```

## Byte gates

The small-order classifier recognizes seven low-255-bit values and ignores the
sign bit, hence fourteen byte strings. They are exactly the encodings the
permissive decoder maps into the eight-point torsion subgroup. All other
strings, including nonsquares, proceed to decoding and fail there if needed.

Canonical R is checked independently of small-order rejection. Let `y` be the
low 255 bits interpreted as a little-endian integer and `s` the high sign bit.
Given successful decoding, the exact byte predicate is

```text
y < p and not (s == 1 and (y == 1 or y == p-1)).
```

The second clause rejects sign-bit-one when `x=0`, which on Edwards25519 occurs
only at `y=1` or `y=-1`. A string may satisfy this byte-form predicate and
still fail decoding because the curve equation has no square root. Keeping
canonicality independent of the small-order helper prevents a future profile
edit or reordering from silently accepting negative zero.

Public-key A deliberately remains permissive. The original A and R bytes—not
re-encodings—enter SHA-512. Mixed-order points are accepted unless the whole
point is pure small order, matching the target predicate.

## Exact scalar semantics

The challenge is reduced canonically modulo `l`, but its signed digit stream
must reconstruct the exact integer `-k`. For radix width `w`, the contract is

```text
sum(d_j * 2^(w*j), j) == -k in Z.
```

Congruence modulo `l` is insufficient. In particular, the implementation does
not replace `-k` by `l-k`: those are equivalent on the prime-order subgroup but
can differ on the torsion component of a mixed-order A. Negating radix digits
is one implementation of this contract, not the contract itself.

## Failure and lane behavior

Signature rejection returns `NARYA_OK` with the lane bit clear. CPU or argument
errors leave the complete verdict byte unchanged. Lane invalidation is
monotone: once a lane is removed from the live mask, no later stage may restore
it. Invalid and inactive lanes become neutral internal values only so the
common SIMD stream remains defined; identity substitution is not part of their
acceptance semantics.

The lane-refinement obligation covers table addresses and indices, transposes
and shuffles, field operations and carries, equality masks, and final verdict
packing. An invalid or inactive lane may not influence any other lane through
any of those boundaries.

The caller owns a reusable workspace satisfying the documented size,
alignment, and non-aliasing contract. It may not overlap public keys,
signatures, messages, or the verdict byte. The implementation performs no
allocation.

## Fixed-base boundary

The verifier uses the immutable radix-256 comb documented in
[`FIXED_BASE_COMB.md`](FIXED_BASE_COMB.md) for `[S]B`. The earlier checkpoint
used the variable-base radix-32 engine for both terms, establishing the whole
predicate before accepting that optimization. That checkpoint is a regression
oracle, not a proof of the replacement. The fixed base has the independent
universal obligation

```text
for every integer S with 0 <= S < l: Comb(S) == [S]B.
```

The obligation covers exact digit reconstruction, every table entry, signs,
indices, offsets and carries, the highest digit, and the boundary scalars
`S=0` and `S=l-1`. Direct comb fixtures and the unchanged complete-verifier
corpus support this obligation but do not substitute for it.

[dalek-verifying]: https://github.com/dalek-cryptography/curve25519-dalek/blob/8016d6d9b9cdbaa681f24147e0b9377cc8cef934/ed25519-dalek/src/verifying.rs
