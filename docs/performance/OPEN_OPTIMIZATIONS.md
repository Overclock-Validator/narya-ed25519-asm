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

## Point-layer fusion — doubling and Niels Stage 2 implemented

The four raw products and direct-XY linear stage of point doubling now execute
in one SysV leaf, followed by separately visible final products. Typed P2
intermediates omit `T` on four of every five dependent doublings. On the dated
Zen 5 run this combination reduced complete x8 verification by 5.8% and
retired instructions by 7.7%.

The analogous projective- and affine-Niels Stage-2 leaves are now implemented
with their own raw-product provenance, `535p` subtraction-bias certificate,
maximum-u52/random differentials, and complete-verifier A/B. Against the
already-fused doubling/P2 baseline, the order-balanced Zen 5 median improved
from 47.94 to 46.77 microseconds per x8 call (2.45%). The emitted Stage-2 bytes
remain an open formal-refinement obligation; do not infer their safety from
the ordinary multiplier or doubling certificates.

## Asymmetric fixed-base injection — implemented

The complete verifier now replaces its separate radix-256 `[s]B` evaluation,
variable-base `[-k]A` evaluation, and final point addition with one merged
schedule. A 120 KiB signed width-10 generator table supplies 26 digits while
the variable term retains its 51 balanced radix-32 digits. Both streams share
the existing 250 doublings.

On a pinned Ryzen 7 9700X, the longer six-sample complete-verifier A/B reduced
the median from 47.265 to 45.376 microseconds per x8 call, or 3.99%. Hardware
counters in a separate run fell 5.31% for cycles, 2.20% for instructions, and
5.05% for task clock. See the
[dated record](../reproducibility/zen5-asymmetric-b10-2026-07-29/README.md).

The improvement is cold: the generator table is immutable process-wide state,
not retained public-key state. The abstract-group recurrence is documented,
but a machine-checked recoder/table/C-schedule refinement remains open.

## Compressed finalizers — single-group negative, cross-group implemented

A native prototype removed the full `R` square-root decode, compared
`Y_Q = y_R Z_Q` projectively, and used one x8 inversion to recover only the
affine-`X` sign. Direct inversion, alias, projective-rescaling, opposite-sign,
zero-`Z`, complete-corpus, and sanitizer gates passed.

Against `fe951d35d59fb8299d1da5a7ae5a4ed27b8959f7`, six order-balanced
100,000-call samples regressed from a 44.857 to 45.782 microsecond median per
x8 group, or 2.06%. The production prototype was therefore removed.

That negative remains the reason counts through eight retain decode-R and the
projective comparison. The public 1..64 API now implements the previously
missing multi-group regime: for wider batches it keeps each equation point,
shares one Montgomery inversion across all x8 groups, canonically encodes each
point, and compares the original `R` bytes.

On a pinned Ryzen 7 9700X, paired medians versus repeated exact x8 calls were
neutral at 8, 1.24% faster at 16, 4.11% faster at 32, and 2.40% faster at 64.
The non-monotone 64 result is retained rather than smoothed away; the larger
equation/prefix/inverse working set is a plausible cache cost and remains a
profiling question. See the
[dated record](../reproducibility/zen5-batch-finalization-2026-07-29/README.md).
