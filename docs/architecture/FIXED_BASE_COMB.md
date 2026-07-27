# Immutable radix-256 fixed-base comb

The `[S]B` term uses a process-shared 480 KiB read-only table. This removes the
variable-base path's 250 doublings and per-call basepoint-table construction.
Cold public keys still retain no state between calls.

## Integer decomposition

A canonical scalar is recoded into 32 balanced radix-256 digits
`d_0..d_31`, each in `[-128,127]`, with the exact identity

```text
s = sum(d_j * 2^(8j), j=0..31).
```

For position `i`, the table base is `P_i=[2^(16i)]B` and its entries are
`[m]P_i` for magnitudes `m=1..128`, with both signs stored. Evaluation first
adds every odd digit, doubles the accumulator eight times, and then adds every
even digit:

```text
[2^8] sum(d_(2i+1) P_i) + sum(d_(2i) P_i)
  = sum(d_j [2^(8j)]B)
  = [s]B.
```

The schedule needs at most 32 mixed additions and exactly eight doublings.

## Binary table format

`data/narya_fixed_base_comb_r256.bin` is laid out as:

```text
[16 positions][128 magnitudes][2 signs][5 limbs][3 coordinates]uint64_le
```

The coordinates are affine Niels `(Y+X, Y-X, 2dXY)`. Each sign entry is 120
bytes; the complete payload is 491,520 bytes and has SHA-256:

```text
a2b3b3601e677cf7466a4f3a8f0760e933fe39e7fcfad569b349068ceec9f022
```

The dependency-free generator uses Python big integers and affine Edwards
addition. `src/fixed_base_comb_data.S` embeds the result in `.rodata`; the
payload is immutable and naturally shared by all workers.

## Assembly selector

`src/affine_niels_transpose_x8.S` accepts eight independently chosen entry
pointers. Each five-limb row contains exactly three qwords, so masked
`VMOVDQU64` loads with `K1=0b0111` avoid overreading the 120-byte boundary.
Two 4x4 qword transposes place the selected coordinates into eight arithmetic
lanes. The fourth shuffled column is zero and is never stored.

Inactive and zero-digit lanes point at the affine-Niels identity `(1,1,0)`.
All scalar digits are public, so direct table indexing does not expose secret
material. Lane/tag tests and complete point fixtures ensure that a pointer or
shuffle error cannot silently exchange verdict lanes.

## Independent gates

`tools/generate_fixed_base_comb.py` also emits 32 heterogeneous x8 groups of
scalar-order edges and deterministic random scalars. The native test compares
the comb output projectively to affine big-integer scalar multiplication and
sweeps all 256 active masks. The complete strict-verifier corpus is rerun after
the fixed-base substitution.
