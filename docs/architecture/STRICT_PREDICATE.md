# Strict verification predicate

The public ABI implements one through 64 independent instances of this
predicate in x8 groups. Let `S` be the unsigned little-endian integer
represented by all 32 original `S_bytes`:

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
Every accepted lane must decode `A_bytes`. The x8 finalizer also decodes
`R_bytes`; the wider finalizer instead proves `R` decodable implicitly by
requiring the canonical encoding of a valid equation point to equal the
original `R_bytes`.

This is an equivalent restatement of the pinned
[ed25519-dalek 2.x `verify_strict` source][dalek-verifying]. Dalek performs the
last two requirements together by compressing `Q` and comparing its bytes to
the original signature `R`. Narya establishes canonical `R` before the
equation. Its single-group route then uses two projective cross-products:

```text
field_equal(X_Q * Z_R, X_R * Z_Q)
field_equal(Y_Q * Z_R, Y_R * Z_Q)
```

`field_equal` means equality in `F_p`, not equality of the redundant five-limb
representations. Successful decoding establishes `Z_R != 0`; the point
arithmetic contract must establish that `Q` is a valid projective Edwards point
with `Z_Q != 0`. No field inversion or point serialization is needed at the
final boundary.

For wider batches, Narya does not decode `R`. It computes the same valid
projective `Q`, batch-inverts the `Z_Q` denominators across groups, canonically
encodes each affine point, and compares those 32 bytes with the original
`R_bytes`. Equality itself establishes that `R_bytes` encodes the same valid
point. The original bytes still enter the hash and final comparison.

The equivalence obligation is explicit: for every successfully decoded
`R_bytes` and valid projective `Q`,

```text
canonical(R_bytes) and projective_equal(Q, Decode(R_bytes))
    iff Encode(Q) == R_bytes.
```

Thus the two production finalizers implement the same terminal predicate. The
cross-group inversion is only an arithmetic sharing device: prefixes are
formed independently in each of the eight SIMD lanes, and no signature
equation or verdict is combined with another.

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

The verifier uses the immutable B10 table and merged double-scalar schedule
documented in
[`ASYMMETRIC_FIXED_B10.md`](ASYMMETRIC_FIXED_B10.md). The independent
radix-256 comb remains a structurally different regression oracle. Earlier
checkpoints also used the variable-base radix-32 engine for both terms,
establishing the complete predicate before either fixed-base optimization was
accepted. Those checkpoints are evidence, not proofs of the replacement. The
fixed base has the independent universal obligation

```text
for every integer S with 0 <= S < l: B10(S) == [S]B.
```

The obligation covers exact digit reconstruction, every table entry, signs,
indices, offsets and carries, the highest digit, and the boundary scalars
`S=0` and `S=l-1`. The merged evaluator additionally has to preserve the exact
`-k` integer action on mixed-order `A` and refine the documented 250-doubling
event recurrence. Direct B10-versus-radix-256 differentials and the unchanged
complete-verifier corpus support these obligations but do not substitute for
them.

[dalek-verifying]: https://github.com/dalek-cryptography/curve25519-dalek/blob/8016d6d9b9cdbaa681f24147e0b9377cc8cef934/ed25519-dalek/src/verifying.rs
