# Native fuzzing

`fuzz_verify_strict_x8.c` interprets each input as an active mask, eight public
keys, eight signatures, eight bounded message lengths, and message bytes. On
native IFMA hardware it requires:

- deterministic repeated verdicts;
- no verdict bit outside the active mask; and
- exact agreement between each lane evaluated in the batch and by itself.

The committed corpus is generated deterministically from the external strict
verification vectors. Reproduce it with `make check-generated` and build the
Clang libFuzzer target with:

```sh
make fuzz-build
./build/fuzz_verify_strict_x8 tests/fuzz/corpus/verify_strict_x8
```

The target returns immediately on unsupported hardware. A successful run on
such a host is therefore not native-verifier evidence; CI compilation and
corpus-schema validation remain useful but are labeled separately.
