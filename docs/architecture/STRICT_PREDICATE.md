# Strict verification predicate

The public ABI implements eight independent instances of this predicate:

```text
require S_bytes < l
reject A_bytes if permissive_decode(A_bytes) is pure small order
reject R_bytes if permissive_decode(R_bytes) is pure small order
require R_bytes to be a canonical compressed Edwards encoding
A = permissive_decode(A_bytes)
R = permissive_decode(R_bytes)
k = SHA512(original_R_bytes || original_A_bytes || message) mod l
Q = [S]B - [k]A
accept iff Q = R
```

This is an equivalent restatement of ed25519-dalek 2.x `verify_strict`. Dalek
performs the last two requirements together by compressing `Q` and comparing
its bytes to the original signature `R`. Narya establishes canonical `R`
before the equation and then uses two projective cross-products:

```text
X_Q * Z_R == X_R * Z_Q
Y_Q * Z_R == Y_R * Z_Q
```

No field inversion or point serialization is needed at the final boundary.
The equivalence obligation is explicit: for a successfully decoded R,
`canonical(R_bytes) and Q=R` if and only if `Encode(Q)=R_bytes`.

## Byte gates

The small-order classifier recognizes seven low-255-bit values and ignores the
sign bit, hence fourteen byte strings. They are exactly the encodings the
permissive decoder maps into the eight-point torsion subgroup. All other
strings, including nonsquares, proceed to decoding and fail there if needed.

Canonical R is checked independently of small-order rejection. It requires
the encoded y value to be below `p=2^255-19` and rejects sign-bit-one when
`x=0`, which on Edwards25519 occurs only at `y=1` or `y=-1`. Keeping this helper
ordering-independent prevents a future profile edit from silently accepting
negative zero.

Public-key A deliberately remains permissive. The original A and R bytes—not
re-encodings—enter SHA-512. Mixed-order points are accepted unless the whole
point is pure small order, matching the target predicate.

## Exact scalar semantics

The challenge is reduced canonically modulo `l`, but negating its public-key
term is an exact integer negation of the radix digits. The implementation does
not replace `-k` by `l-k`: those are equivalent on the prime-order subgroup but
can differ on the torsion component of a mixed-order A.

## Failure and lane behavior

Signature rejection returns `NARYA_OK` with the lane bit clear. CPU or argument
errors leave the complete verdict byte unchanged. Invalid and inactive lanes
become identities internally and cannot influence another lane's table entry,
field arithmetic, or verdict. The public caller owns a reusable non-overlapping
workspace; the implementation performs no allocation.

## Current performance boundary

The ABI-zero checkpoint uses the variable-base radix-32 engine for both terms.
That makes the whole predicate testable before the fixed-base optimization is
trusted. Replacing `[S]B` by a fixed-base comb changes only an implementation
of scalar multiplication and must remain differential-equivalent to this
checkpoint.
