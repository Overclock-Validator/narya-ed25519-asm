# Merged asymmetric fixed-base schedule

The complete cold verifier evaluates `[s]B-[k]A` with one accumulator and one
250-doubling chain. The variable point keeps the existing balanced radix-32
table. The immutable generator uses balanced radix-1024 digits and a one-row
signed table containing `[1]B` through `[512]B`.

This is still eight independent verification equations. Nothing is aggregated
across lanes, no random coefficient is introduced, and no public-key state is
retained between calls.

## Exact scalar decompositions

For every canonical `s,k` in `[0,l)`, the two recoders establish exact integer
identities, not merely congruences modulo `l`:

```text
s  = sum(b[j] * 2^(10j), j=0..25),  b[j] in [-512,511]
-k = sum(a[i] * 2^(5i),  i=0..50),  a[i] in [-16,15]
```

Canonical scalars are below `2^253`. Twenty-six ten-bit windows therefore
cover every input and absorb the final balanced carry. Both decompositions'
highest possible exponent is 250, which is the fact that lets them share a
chain without adding a doubling.

The implementation applies the minus sign to the `k` digits as an exact
integer operation. Replacing `-k` with `l-k` would be wrong for a public point
with a torsion component, even though the two scalars agree on the prime-order
subgroup.

## Event schedule and group-law proof

For blocks `j=25..0`, `src/asymmetric_fixed_b10.c` performs:

```text
Q <- Q + [b[j]]B + [a[2j]]A
if j > 0:
    Q <- [2^5]Q + [a[2j-1]]A
    Q <- [2^5]Q
```

One non-final block therefore transforms `Q` into

```text
[2^10]Q + [b[j] * 2^10]B
           + [a[2j] * 2^10 + a[2j-1] * 2^5]A.
```

Expanding the recurrence through the final block gives exactly

```text
Q = [sum(b[j] * 2^(10j))]B +
    [sum(a[i] * 2^(5i))]A
  = [s]B - [k]A.
```

This proof is over an abstract group and is independent of coordinate
formulas. The remaining implementation obligations are that both recoders
produce the stated digits, table selection returns the requested signed
multiple in the correct lane, every point operation implements the group
operation, and the C event order refines the recurrence above.

## Immutable B10 table

`data/narya_fixed_base_b10.bin` has layout:

```text
[512 magnitudes][2 signs][5 limbs][3 affine-Niels coordinates]uint64_le
```

The coordinates are `(Y+X, Y-X, 2dXY)`. Each signed entry is 120 bytes; the
payload is 122,880 bytes and has SHA-256:

```text
82c05fbe7a74131355010cbd3605fae76630f3df0e991917a0ba11697bdb9d7d
```

`tools/generate_fixed_base_comb.py` generates the payload with Python big
integers and affine Edwards addition. `tools/check_generated.py` regenerates
it and compares every byte. `src/fixed_base_comb_data.S` embeds it in
read-only storage. Public verification digits permit direct indexing.

The older two-row radix-256 comb remains in the repository as a structurally
different differential oracle: it uses a different scalar decomposition,
table geometry, event order, and doubling schedule.

## Native gates

`tests/test_scalar_mult_x8.c` compares the merged evaluator against the
deliberately separate construction `[s]B + [-k]A` over 32 heterogeneous x8
groups. It also sweeps all 256 active masks and verifies that a noncanonical
`s` invalidates only its own lane. The complete verifier then checks accepted
signatures against independently generated RFC/CCTV/Wycheproof and boundary
vectors, which prevents a shared fixed-base generator mistake from being the
only oracle.

These tests and the algebra above do not yet constitute a byte-linked proof of
the C schedule or table payload. That refinement remains explicit in the
formalization backlog.
