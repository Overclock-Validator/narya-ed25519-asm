# Exact cross-group batch finalization

## Scope

`narya_ed25519_verify_strict_batch` verifies one through 64 independent cold
signatures. It is a dispatcher and arithmetic-amortization API, not randomized
aggregate verification. Input `i` always maps to verdict bit `i`; no equation
can cancel another.

Counts through eight delegate to `narya_ed25519_verify_strict_x8`, which
permissively decodes `R` and compares the equation point projectively. Wider
batches use the equivalent terminal check

```text
Encode([S]B - [k]A) == original_R_bytes.
```

This avoids decoding `R` in every x8 group and shares the one expensive field
inversion needed for encoding across as many as eight groups.

## Preparation

For each x8 group, the wide route applies the same byte gates, segmented hash,
scalar reduction, permissive `A` decode, public-key table construction, and
merged B10 double-scalar multiplication as the x8 route. It deliberately does
not decode `R`. The resulting projective equation point is

```text
Q_g,l = (X_g,l : Y_g,l : Z_g,l),
```

for group `g` and SIMD lane `l`. Each lane's live bit remains monotone. A dead
lane is never allowed to contribute a verdict.

## Lane-wise Montgomery inversion

Within each fixed SIMD lane, inactive group denominators are replaced by one:

```text
z'_g,l = Z_g,l  when lane l is live in group g
         1      otherwise.
```

The implementation forms prefixes

```text
P_0,l = z'_0,l
P_g,l = P_(g-1),l * z'_g,l.
```

It inverts only the final vector `P_(groups-1)`. A backward sweep recovers
every live `1/Z_g,l`. All multiplications are component-wise r51x8 operations;
there is no horizontal operation and therefore no cross-lane arithmetic.

Before inversion, an active zero in the final product returns
`NARYA_ERR_INTERNAL`. In a field, that product is zero exactly when some live
denominator in the same lane is zero. This check makes a violated projective
point invariant visible rather than silently encoding a zero denominator.
Inactive denominators remain one and cannot cause the fault.

The inverse exponent is exact for `p = 2^255-19`:

```text
x^(p-2) = (x^(2^252-3))^8 * x^3.
```

The first exponent is the decoder's existing `pow22523` addition chain. Direct
field tests cover zero, maximum-u52 inputs, heterogeneous random lanes, and
exact source/output aliasing.

## Encoding and predicate equivalence

For each live equation point, the finalizer computes

```text
x = X / Z
y = Y / Z
```

and canonically reduces both r51 values. It serializes canonical `y` and puts
the parity of canonical `x` in bit 255. The result is compared byte-for-byte
with the original signature `R`; those same original bytes were used in the
challenge hash.

For a valid projective Edwards point `Q`, `Encode(Q)` is necessarily a
canonical, decodable compressed point. Therefore equality with the original
bytes simultaneously establishes `R` decodability, point equality, canonical
`y`, and the required `x` sign. Combined with the independent byte prechecks
for canonical `R` and pure-small-order `R`, this is equivalent to the
single-group decode/projective-compare route and to the pinned terminal dalek
byte comparison. See [`STRICT_PREDICATE.md`](STRICT_PREDICATE.md).

## Failure and memory behavior

- Argument, CPU, or internal-arithmetic errors leave the caller's complete
  64-bit verdict unchanged.
- The only partial group is padded into readable local rows before any x8
  routine can load it.
- The batch workspace is caller-owned and contains one reusable public-key
  table plus equation, prefix, and inverse arrays for eight groups.
- The implementation allocates no memory and publishes the staged verdict only
  after every group and the finalizer succeed.

## Evidence and open proof boundary

Native tests cover counts 1, 2, 4, 8, 9, 17, 32, 63, and 64; group-boundary
late failures; API atomicity; field inversion; and all 2,954 committed external
vectors through both the batch API and the established x8 grouping oracle.
ASan and UBSan pass on native IFMA hardware.

These tests are evidence, not a universal proof. A future formal refinement
should prove the prefix/backward identities lane-wise, the inversion exponent,
canonical r51 serialization, exact input-index-to-verdict-bit mapping, the
active-zero fault condition, and equivalence with the strict predicate.
