/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Narya's DalekStrict Ed25519 verification predicate, executable.

Structure follows `NaryaFormal.VerificationSpine.DalekStrict` field for
field: canonical `s`, both encodings decode, neither point has small order,
`R` is canonically encoded, and the cofactorless equation
`[s]B - [k]A = R` holds with `k = SHA-512(R || A || M) mod L`. The hash
consumes the original `R` and `A` bytes, so a noncanonical `A` encoding is
hashed as given.

This is also the predicate Mithril reaches through `narya.VerifyStrict`: Go's
`crypto/ed25519.Verify` plus rejection of small-order `A` and `R`.
-/

import NaryaSpec.Bytes
import NaryaSpec.Sha512
import NaryaSpec.Edwards

namespace NaryaSpec

/-- The prime order of the basepoint subgroup. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- The challenge scalar: the 64-byte digest read little-endian, mod `L`. -/
def challenge (rBytes aBytes message : ByteArray) : Nat :=
  leNat (Sha512.hash (rBytes ++ aBytes ++ message)) % L

/-- DalekStrict verification of a 64-byte signature by a 32-byte public key. -/
def verifyStrict (publicKey message signature : ByteArray) : Bool :=
  if publicKey.size ≠ 32 ∨ signature.size ≠ 64 then false
  else
    let rBytes := signature.extract 0 32
    let s := leNat (signature.extract 32 64)
    if s ≥ L then false
    else
      match Point.decode publicKey, Point.decode rBytes with
      | some A, some R =>
          !A.smallOrder && !R.smallOrder && R.encode.data == rBytes.data &&
            Point.sub (Point.nsmul s Point.basepoint)
              (Point.nsmul (challenge rBytes publicKey message) A) == R
      | _, _ => false

end NaryaSpec
