# Decoder fixture provenance

`narya_permissive_decode_v1.txt` pins 256 compressed-input decisions and full
extended Edwards coordinates from Narya's scalar radix-2^51 decoder.  The
fixture intentionally includes canonical encodings, every possible
noncanonical low-255-bit interval value (`p` through `p+18`) with both sign
bits, negative zero, small-order edge values, nonsquares, and deterministic
pseudorandom inputs.

It was generated from Narya Ed25519 commit
`13dc06d4a5f0ad8be62412a89de3a44de57bd504` with:

```text
go run ./cmd/narya-decode-fixtures -count 256
```

The generator uses the scalar `internal/r51x5.Point.SetBytes` path, never the
standalone assembly implementation.  Invalid inputs are recorded with the
identity coordinates because inactive and invalid native lanes must fail
closed to the identity.  The C differential checks coordinates modulo
`2^255-19`, so it does not accidentally require one particular redundant
limb representation.

Regeneration is an explicit review event: update the pinned source commit,
inspect the semantic diff, and rerun the native and sanitizer gates.
