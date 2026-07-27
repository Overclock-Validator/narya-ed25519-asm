# Zen 5 point/decode checkpoint — 2026-07-27

This record covers standalone assembly commit
`16927e0eaf629b43c8bb3188d701e79f50f7e938`.

## Scope

- r51×8 multiply, add, subtract, and negate;
- maximum-u52 and 10,000 deterministic random field inputs;
- exact source/output aliases and output-atomic range failures;
- 256 chained point doublings;
- projective-Niels conversion and heterogeneous-lane mixed addition;
- permissive compressed-point decode;
- 256 pinned scalar-Go decoder vectors, including canonical, noncanonical,
  small-order, nonsquare, sign-bit, inactive-lane, and random cases;
- warning-as-error compilation and ASan/UBSan execution.

## Verdict

All listed gates passed on the Ryzen 7 9700X. The fixture source is pinned in
`tests/vectors/README.md`. This is evidence for the current field, point, and
decoder layers; it is not evidence for a complete signature verifier.
