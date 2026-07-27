# Zen 5 field/point checkpoint — 2026-07-27

This is the first native execution gate for the standalone System V port.

## Scope

- r51×8 multiply, add, subtract, and negate;
- exact `out == x` and `out == y` aliases where applicable;
- zero and maximum-u52 boundary inputs;
- 10,000 deterministic random x8 input pairs;
- 256 chained extended-coordinate doublings of the canonical basepoint;
- in-place point doubling at every step.

The native outputs were compared bit-for-bit with portable scalar oracles. The
oracles model the IFMA low/high split using `__uint128_t` and do not share the
assembly macros or register schedule.

## Verdict

All tests passed on the Ryzen 7 9700X. This is evidence for the listed kernels,
not evidence that a complete standalone signature verifier exists yet.
