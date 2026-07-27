# Projective-Niels table and selector

The cold variable-base path prepares sixteen positive multiples of each of
eight public keys. Each point is stored per key as five contiguous rows of
`[Y+X,Y-X,Z,2dT]`, 160 bytes per entry. Both public signs are retained:
negation swaps the first two coordinates and negates `2dT`.

At evaluation time each lane can request a different sign and magnitude. The
selector chooses eight entry pointers, substitutes the Niels identity for
zero/inactive lanes, and enters a no-stack assembly leaf. Ten independent
4x4 qword transposes turn the per-key rows into the structure-of-arrays layout
used by x8 field arithmetic.

Pre-signing doubles the cold table payload but removes per-round field
negation and sign-swapping from the selector. This is the selected Zen 5
shape in the Go implementation; the standalone port retains it so the C ABI
does not begin with a known-obsolete diagnostic layout.

The transpose gate fills every source cell with a unique tag and sweeps all
256 active masks with varying signs and magnitudes. A separate group-law
fixture is still required before table construction may feed the DSM; the
identity-table test alone proves layout/sign mechanics, not arbitrary-point
multiples.
