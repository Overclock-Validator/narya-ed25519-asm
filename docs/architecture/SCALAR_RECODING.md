# Scalar recoding

The cold x8 verifier uses a balanced radix-32 schedule for the variable-base
term. Fifty-one round-major records hold eight public digits each. Every digit
lies in `[-16,15]`; the table stores positive multiples `1P` through `16P`,
and a sign mask tells the selector when to negate the cached point.

The exact-integer sign is consensus-relevant. The verification equation uses
`[S]B - [k]A`. Narya recodes canonical `k` and negates its signed digits. It
does **not** replace `-k` by the scalar-field representative `l-k`, because
those coefficients act differently on a public key with a torsion component.

The implementation computes records in consumer order, validates every input
against the literal group order, zeros invalid and inactive lanes, and returns
the valid-lane mask. Tests reconstruct each expansion as a signed 320-bit
integer and compare it with `S` or `-k`; this is stronger than checking only
modulo `l`.
