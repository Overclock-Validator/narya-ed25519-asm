# Zen 5 coordinate-packed small-batch checkpoint — 2026-07-29

This record characterizes commit
`a5875fe79b13ee3487b193d8cd380eba1c27fb3a`. The implementation routes n=1
and n=2 through two coordinate-packed point chains in one ZMM register, fuses
the point layer's first and final multiplication operands into the r51
schedule, hashes small batches with an independent scalar FIPS-180-4 SHA-512,
and retains the existing x8 path for n>=3.

## Scope

- Public `narya_ed25519_verify_strict_batch` API.
- Valid cold signatures; no public-key state retained between calls.
- One pinned logical CPU, performance governor, `GOMAXPROCS` not applicable.
- Nine samples at each width and message size.
- Message sizes 200, 1232, and 4096 bytes from the committed strict fixture.
- Results are microseconds per signature; lower is better.

## Median complete-verifier results

| Message bytes | n=1 | n=2 | n=4 | n=8 | n=64 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 200 | 13.284 | 7.040 | 6.589 | 3.539 | 3.245 |
| 1232 | 14.580 | 8.356 | 8.382 | 4.715 | 4.520 |
| 4096 | 18.253 | 12.020 | 13.330 | 8.461 | 7.312 |

The n=2 and n=4 ordering is not a typo. n=2 fills one ZMM with two
coordinate-packed chains; n=4 occupies half of the signature-parallel x8
layout. The dispatcher retains x8 at n=4 because two separate packed-pair
calls regress 200-byte verification and do not materially improve the
1232-byte target.

## Same-binary 1232-byte strategy A/B

| Count | Padded signature-x8 | Packed public path | Change |
| ---: | ---: | ---: | ---: |
| 1 | 28.947 us/sig | 14.579 us/sig | -49.6% |
| 2 | 15.274 us/sig | 8.513 us/sig | -44.3% |

The A/B uses one binary and alternates order. It compares the new public route
with the prior strategy of padding the same inputs into the x8 verifier; it is
not a comparison with another library.

## Correctness gates

- Warning-as-error native suite: pass.
- ASan/UBSan native suite: pass.
- All 2,954 external vectors at n=1, adjacent n=2, and wide x8: pass.
- Scalar SHA-512 versus the independent scalar oracle and x8 assembly across
  lengths 0, 1, 47, 48, 64, 200, 1232, and 4096: pass.
- Fused packed leaves versus split operands plus the reviewed r51 multiply at
  maximum-u52 and 256 heterogeneous random inputs, with alias cases: pass.

One early native run faulted because newly introduced constant loads used
`VMOVDQA64` against data guaranteed only 16-byte alignment. The loads were
changed to `VMOVDQU64` before any benchmark was accepted; the external corpus,
direct differentials, Werror suite, sanitizer suite, and final measurements
all use the corrected code.

## Interpretation boundary

These results apply only to the named commit, CPU, compiler, fixture, and
commands. They are cold-verification numbers, not warm-cache results. They do
not establish Zen 4 performance, a general CPU dispatch policy, or correctness
of physical AVX-512 hardware.
