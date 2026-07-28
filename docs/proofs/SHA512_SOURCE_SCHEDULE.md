# SHA-512 x8 source-schedule certificate

`src/sha512x8.S` implements eight independent SHA-512 compression functions
with a sixteen-register rolling message schedule and rotating macro arguments
for `a..h`. Those choices remove memory traffic, but make a one-position ring
or working-register error difficult to detect by visual inspection.

## Checked specification

The reference is [NIST FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4).
For every lane, the checked source must implement:

```text
W[t] = W[t-16] + sigma0(W[t-15]) + W[t-7] + sigma1(W[t-2])

sigma0(x) = ROTR1(x)  xor ROTR8(x)  xor SHR7(x)
sigma1(x) = ROTR19(x) xor ROTR61(x) xor SHR6(x)
Sigma0(x) = ROTR28(x) xor ROTR34(x) xor ROTR39(x)
Sigma1(x) = ROTR14(x) xor ROTR18(x) xor ROTR41(x)
```

with the standard `Ch`, `Maj`, eighty constants, round update, and
Davies–Meyer feed-forward, all modulo `2^64`.

## Executable source certificate

[`check_sha512_schedule.py`](../../tools/check_sha512_schedule.py) parses the
actual assembly source and fails closed if its small accepted grammar changes.
It checks:

1. every one of the 80 literal round constants against FIPS 180-4;
2. the exact rotate/shift counts in the small and capital sigma functions;
3. by exhaustive one-bit truth tables, that `VPTERNLOGQ` immediates `0xca`,
   `0xe8`, and `0x96` implement `Ch`, `Maj`, and three-input XOR under the
   Intel operand ordering;
4. every round's rotating `a..h` register arguments;
5. every expanded word's rolling-ring registers, proving that the operands
   currently represent `W[t-16]`, `W[t-15]`, `W[t-7]`, and `W[t-2]`;
6. every round-constant byte offset and `W[t]` register;
7. all sixteen block loads, eight state loads, eight feed-forward additions,
   and eight state stores in word order.

Because the accepted macro templates contain only packed qword rotates,
shifts, ternary logic, additions, broadcasts, and moves, they contain no
horizontal or shuffle operation capable of mixing lanes.

Run it with:

```sh
make check-sha512-schedule
```

It also runs under `make check-source` and hosted CI.

## Independent execution evidence

The native C suite does not reuse the rolling schedule. It expands all eighty
words in a scalar array and compares 2,000 deterministic random
state/block pairs. It also checks the FIPS empty-message digest, an external
known answer, all 256 active masks, independent lane data, unequal message
lengths, and padding boundaries through 4096-byte messages.

## Remaining trust boundary

This certificate is not a proof over the assembled ELF bytes. It trusts the
small Python parser, Intel instruction semantics, assembler encoding, and CPU
execution. It also covers the compression leaf, not the C scheduler's byte
gathering, big-endian transposition, padding, or final digest capture. Those
wrapper properties currently have differential tests but no universal proof.

An eventual binary-refinement theorem should connect decoded opcodes to the
same round/ring trace. A separate wrapper theorem should cover the SHA-512
128-bit length field, `R || A || message` byte order, active-lane completion,
and error atomicity.
