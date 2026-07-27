# Variable-base scalar multiplication

The cold x8 path evaluates eight unrelated signed scalar multiplications in
parallel. Each lane has its own canonical scalar, base point, sign, and active
bit. The lanes share instructions but never field values or verdict state.

## Exact integer schedule

`narya_scalar_recode_radix32_x8` produces 51 balanced radix-32 digits in
`[-16,15]`. For lane `i` it proves the integer identity

```text
signed_scalar_i = sum(round_digit_i[r] * 32^r, r=0..50).
```

The sign is applied to the digits. It is deliberately not implemented as
`l-k`: those expressions agree on the prime-order subgroup but can disagree
on an Edwards point with a torsion component. The strict verifier must retain
exact signed-integer semantics.

The multiplier walks the digits from most to least significant. Between
rounds it doubles the accumulator five times, then adds the selected signed
multiple. This is ordinary Horner evaluation in the Edwards group:

```text
Q <- identity
for r = 50 .. 0:
    if r != 50: Q <- [32]Q
    Q <- Q + [digit[r]]P
```

## Table boundary

The table stores magnitudes 1 through 16 in projective-Niels form, with both
signs precomputed. Zero and inactive lanes select the Niels identity. See
[`PROJECTIVE_NIELS_TABLE.md`](PROJECTIVE_NIELS_TABLE.md) for its storage and
assembly-transpose contract.

The table builder and point evaluator currently coordinate the audited
assembly field leaves from C. This is intentional: the public goal is a
standalone native library with no Go runtime, while keeping policy and loop
structure visible until the complete equation has a stable profile. A later
superkernel may replace this schedule only behind the same differential gate.

## Differential evidence

`tools/generate_variable_scalar_vectors.py` is an independent affine
big-integer implementation. It generates 32 heterogeneous x8 groups using
base points `[1]B` through `[8]B`, scalar-order edges, full-width deterministic
random scalars, and both exact signs. It shares no recoder, projective formula,
table layout, or native field routine with the implementation.

The native test additionally sweeps all 256 active masks and injects `l` into
one lane to verify lane-local rejection of a noncanonical scalar. Results are
compared projectively with independently decoded expected encodings.
