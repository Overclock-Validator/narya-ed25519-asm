# System V ABI and data layouts

## Stability

`NARYA_ED25519_ASM_ABI_VERSION` is zero. The field functions are review and
integration scaffolding, not a frozen public API. Version one will begin only
when the complete verifier input/output contract is implemented and reviewed.

## Calling convention

The first target is 64-bit System V AMD64. C entry points use the platform ABI.
Internal assembly leaves receive pointers in the normal integer argument
registers, use only caller-saved vector state, do not allocate stack frames,
and execute `VZEROUPPER` before returning.

Windows x64 is out of scope for the first release and requires a separate shim;
it must not call these leaves under an assumed SysV register contract.

## r51×8 layout

```c
uint64_t limb[5][8];
```

The outer index is radix limb and the inner index is SIMD lane. Five adjacent
64-byte regions can therefore be loaded directly into five ZMM registers. The
native leaves use unaligned loads and stores, so ABI callers do not need to
over-align the structure.

Each lane is independent. Field code may not horizontally reduce, shuffle one
lane into another, or use another lane to decide a result. Table-transpose and
masked-selection kernels added later must document their permitted cross-lane
movement separately and prove that data returns to the correct verdict lane.

## Errors and output atomicity

Checked C entry points validate pointers, CPU/OS support, and external range
contracts before entering unchecked assembly. If a checked call returns an
error, its output must remain unchanged. Internal leaves have no error path and
may only be called when the enclosing schedule proves their preconditions.

## Aliasing

Exact `out == x` and `out == y` aliases are supported only where the header
says so. The implementation establishes this by loading all source vectors
before the first output store. Partial overlap is not supported unless a later
API explicitly defines it.
