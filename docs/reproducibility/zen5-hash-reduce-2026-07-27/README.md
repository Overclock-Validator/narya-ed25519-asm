# Zen 5 hash/reduction checkpoint — 2026-07-27

This record covers standalone assembly commit
`5f449bad19bf190183181f4f96692b830d7b70d6`.

## Scope

- x8 rolling-register SHA-512 compression;
- exact `SHA512(original_R || original_A || message)` scheduling over all 256
  active masks and messages through 4096 bytes;
- FIPS and external SHA-512 known answers;
- x8 signed-radix-`2^21` reduction modulo the Ed25519 scalar order;
- literal scalar-order edges, all 256 active masks, exact input/output alias,
  canonical-output checks, and 10,000 random x8 reductions;
- no-stack disassembly check of the native reduction leaf;
- warning-as-error compilation and ASan/UBSan execution.

## Verdict

All listed gates passed on the Ryzen 7 9700X. Scalar-reduction tests use an
independent 512-step bitwise modulo-order oracle rather than the assembly's
radix, fold constants, carries, or output packing. This is evidence for the
hash and scalar-reduction seams, not for a complete signature verifier.
