/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Byte-string conventions shared by the executable Ed25519 specification.
Everything here is plain Lean core: no Mathlib, no foreign code, and no
`implemented_by`, so the compiled checker runs exactly these definitions.
-/

namespace NaryaSpec

/-- Unsigned little-endian value of a byte string. -/
def leNat (bytes : ByteArray) : Nat :=
  bytes.toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0

/-- The low `width` bytes of `n`, little-endian. -/
def natToLE (n width : Nat) : ByteArray :=
  ⟨((List.range width).map fun i => (n / 256 ^ i % 256).toUInt8).toArray⟩

/-- The low `width` bytes of `n`, big-endian. -/
def natToBE (n width : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun i => (n / 256 ^ i % 256).toUInt8).toArray⟩

/-- Concatenate byte strings (helper with a stable name for later proofs). -/
def concatBytes (parts : List ByteArray) : ByteArray :=
  parts.foldl (· ++ ·) ByteArray.empty

end NaryaSpec
