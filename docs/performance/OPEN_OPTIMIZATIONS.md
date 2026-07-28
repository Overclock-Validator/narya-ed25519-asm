# Open performance investigations

This file records hypotheses so later work remeasures them instead of either
forgetting them or treating an old estimate as a verdict. None of the items
below is a supported performance claim.

## Dedicated r51×8 square

Compressed-point decoding currently implements every square with the general
25-product multiplication leaf. A symmetry-reduced five-limb square needs 15
distinct products plus exact cross-term doubling. Each strict verification
decodes both A and R and therefore executes two long exponentiation chains.

This is a high-value candidate, but it cannot be promoted on operation counts.
It requires:

1. a scalar oracle that is structurally independent of the assembly;
2. exact bit comparison with general multiplication on `x*x`;
3. an explicit accumulator/fold/carry range certificate;
4. alias and lane-independence tests; and
5. a complete-verifier native benchmark on the supported CPUs.

The corresponding formal obligation is tracked in
[`../proofs/FORMALIZATION_BACKLOG.md`](../proofs/FORMALIZATION_BACKLOG.md).

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

## Point-layer fusion

Point doubling and mixed addition remain scheduled by C over reviewed field
leaves. Fusing linear stages can remove call and memory traffic, but increases
the native audit surface and creates new expression-specific range obligations.
Promote only a schedule with per-expression interval certificates and a
complete-verifier improvement on native hardware.
