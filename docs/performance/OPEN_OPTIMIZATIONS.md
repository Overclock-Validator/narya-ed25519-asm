# Open performance investigations

This file records hypotheses so later work remeasures them instead of either
forgetting them or treating an old estimate as a verdict. None of the items
below is a supported performance claim.

## Dedicated r51×8 decoder square — implemented, proof follow-up open

`narya_r51x8_repeated_square_ifma` now retains each dependent square chain in
ZMM registers and uses 15 distinct products instead of calling the general
25-product multiplication leaf for every square. The decoder still uses the
reviewed general leaf for each addition-chain multiply.

The native gate compares counts 0, 1, 2, 5, 10, 20, 50, 100, and 252 exactly
against the structurally independent `__uint128_t` oracle, including maximum
u52 inputs, heterogeneous random lanes, and exact source/output aliasing. The
source-level range argument is recorded in the
[`r51 field contract`](../proofs/R51_FIELD_CONTRACT.md#dependent-square-chain).

On a pinned Ryzen 7 9700X, ten alternating complete-verifier samples reduced
the mean cold-key x8 call from 53.142 to 50.824 microseconds, or 4.36%. See the
[dated raw result](../reproducibility/zen5-decoder-square-chain-2026-07-28/README.md).

The dedicated leaf's source-generated arithmetic trace and assembled-byte
refinement remain open. They are explicitly tracked in
[`../proofs/FORMALIZATION_BACKLOG.md`](../proofs/FORMALIZATION_BACKLOG.md); the
existing multiplier theorem must not be cited as a proof of this new symbol.

## Segmented SHA-512 marshaling

The current scheduler transposes `R || A || message` into SHA-512 words in C.
It is deliberately transparent, but the message segment is visited byte by
byte and each word is assembled with scalar shifts. For long messages this may
consume a meaningful fraction of verification time even though the compression
rounds themselves are x8 assembly.

Candidate work is a block-oriented transpose with precomputed segment
boundaries and direct big-endian word loads where alignment and segment layout
permit. It must retain arbitrary per-lane message lengths, inactive-lane
non-dereference, exact padding at all block boundaries, and output atomicity.
Measure the complete verifier at 64, 200, 1232, and 4096-byte messages.

## Point-layer fusion — doubling Stage 1+2 implemented

The four raw products and direct-XY linear stage of point doubling now execute
in one SysV leaf, followed by separately visible final products. Typed P2
intermediates omit `T` on four of every five dependent doublings. On the dated
Zen 5 run this combination reduced complete x8 verification by 5.8% and
retired instructions by 7.7%.

The analogous projective-Niels addition remains scheduled by C over separate
field leaves. It is the next fusion candidate, but it needs its own raw-product
provenance, subtraction-bias certificate, native differentials, and
complete-verifier A/B. Do not infer its safety from the doubling certificate.
