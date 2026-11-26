/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

SHA-512 as written in FIPS 180-4, sections 4.1.3, 4.2.3, 5.1.2, 5.3.5 and
6.4. It processes one 128-byte block at a time with a straight message
schedule and no lane batching, so it shares no structure with Narya's x8
compression kernels.
-/

import NaryaSpec.Bytes

namespace NaryaSpec.Sha512

/-- FIPS 180-4 section 4.2.3 round constants. -/
def roundConstants : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- FIPS 180-4 section 5.3.5 initial hash value. -/
def initialState : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def rotr (x n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

def bigSigma0 (x : UInt64) : UInt64 := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39
def bigSigma1 (x : UInt64) : UInt64 := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41
def smallSigma0 (x : UInt64) : UInt64 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)
def smallSigma1 (x : UInt64) : UInt64 := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)
def choose (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)
def majority (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Section 5.1.2 padding: one 0x80 byte, zeros to 112 mod 128, then the
message length in bits as a 128-bit big-endian integer. -/
def pad (message : ByteArray) : ByteArray :=
  let zeros := (112 + 128 - (message.size + 1) % 128) % 128
  message.push 0x80
    ++ ⟨(List.replicate zeros (0 : UInt8)).toArray⟩
    ++ natToBE (8 * message.size) 16

/-- Big-endian 64-bit word at byte offset `offset`. -/
def readWord (bytes : ByteArray) (offset : Nat) : UInt64 :=
  (List.range 8).foldl
    (fun acc i => (acc <<< 8) ||| (bytes.get! (offset + i)).toUInt64) 0

/-- Section 6.4.2 step 1: the 80-word message schedule of one block. -/
def schedule (bytes : ByteArray) (offset : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := #[]
  for t in [0:16] do
    w := w.push (readWord bytes (offset + 8 * t))
  for t in [16:80] do
    w := w.push (smallSigma1 w[t - 2]! + w[t - 7]! + smallSigma0 w[t - 15]! + w[t - 16]!)
  return w

/-- Section 6.4.2 steps 2 to 4: compress one block into the state. -/
def compress (state : Array UInt64) (bytes : ByteArray) (offset : Nat) : Array UInt64 :=
  Id.run do
    let w := schedule bytes offset
    let mut a := state[0]!
    let mut b := state[1]!
    let mut c := state[2]!
    let mut d := state[3]!
    let mut e := state[4]!
    let mut f := state[5]!
    let mut g := state[6]!
    let mut h := state[7]!
    for t in [0:80] do
      let t1 := h + bigSigma1 e + choose e f g + roundConstants[t]! + w[t]!
      let t2 := bigSigma0 a + majority a b c
      h := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
      state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- SHA-512 of a byte string: 64 bytes, each state word big-endian. -/
def hash (message : ByteArray) : ByteArray :=
  let padded := pad message
  let state := (List.range (padded.size / 128)).foldl
    (fun state block => compress state padded (128 * block)) initialState
  concatBytes (state.toList.map fun word => natToBE word.toNat 8)

end NaryaSpec.Sha512
