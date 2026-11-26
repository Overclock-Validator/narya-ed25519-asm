/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

The twisted Edwards curve edwards25519, `-x^2 + y^2 = 1 + d x^2 y^2`.

Points are affine pairs of canonical residues, so structural equality is
point equality. The group law `Point.add` is the textbook affine formula
with one inversion per coordinate. Because `d` is not a square, both
denominators are nonzero for every pair of curve points and the formula is
complete.

`Point.nsmul` computes the same multiples in extended coordinates (Hisil,
Wong, Carter and Dawson 2008, the unified `a = -1` addition) and normalizes
once at the end. That keeps a verification at a few milliseconds instead of
seconds. `Point.nsmulAffine` is the slow double-and-add over `Point.add`;
the checker compares the two, and proving them equal is a recorded proof
obligation for the group-law layer.
-/

import NaryaSpec.Bytes
import NaryaSpec.Field

namespace NaryaSpec

/-- The curve constant `d = -121665 / 121666`. -/
def d : Fe := -(Fe.ofNat 121665) * Fe.inv (Fe.ofNat 121666)

structure Point where
  x : Fe
  y : Fe
  deriving DecidableEq, Repr, Inhabited

namespace Point

def identity : Point := ⟨0, 1⟩

def onCurve (P : Point) : Bool :=
  -(P.x * P.x) + P.y * P.y = 1 + d * P.x * P.x * P.y * P.y

def neg (P : Point) : Point := ⟨-P.x, P.y⟩

/-- Affine addition on `-x^2 + y^2 = 1 + d x^2 y^2`. -/
def add (P Q : Point) : Point :=
  let t := d * P.x * Q.x * P.y * Q.y
  ⟨(P.x * Q.y + P.y * Q.x) * Fe.inv (1 + t),
   (P.y * Q.y + P.x * Q.x) * Fe.inv (1 - t)⟩

def sub (P Q : Point) : Point := add P (neg Q)

/-- `[n]P` by double-and-add over the affine law. Slow; used as a check. -/
def nsmulAffine (n : Nat) (P : Point) : Point :=
  if _h : n = 0 then identity
  else
    let half := nsmulAffine (n / 2) P
    let doubled := add half half
    if n % 2 = 1 then add doubled P else doubled
termination_by n
decreasing_by omega

end Point

/-- Extended twisted Edwards coordinates: `x = X/Z`, `y = Y/Z`, `T = XY/Z`. -/
structure Ext where
  X : Fe
  Y : Fe
  Z : Fe
  T : Fe

namespace Ext

def identity : Ext := ⟨0, 1, 1, 0⟩

def ofPoint (P : Point) : Ext := ⟨P.x, P.y, 1, P.x * P.y⟩

def toPoint (E : Ext) : Point :=
  let zInv := Fe.inv E.Z
  ⟨E.X * zInv, E.Y * zInv⟩

/-- Unified addition for `a = -1` (HWCD 2008, section 3.1, `k = 2d`). It is
complete on edwards25519 and also serves as doubling. -/
def add (A B : Ext) : Ext :=
  let a := (A.Y - A.X) * (B.Y - B.X)
  let b := (A.Y + A.X) * (B.Y + B.X)
  let c := A.T * (d + d) * B.T
  let z := A.Z * 2 * B.Z
  let e := b - a
  let f := z - c
  let g := z + c
  let h := b + a
  ⟨e * f, g * h, f * g, e * h⟩

def nsmul (n : Nat) (E : Ext) : Ext :=
  if _h : n = 0 then identity
  else
    let half := nsmul (n / 2) E
    let doubled := add half half
    if n % 2 = 1 then add doubled E else doubled
termination_by n
decreasing_by omega

end Ext

namespace Point

/-- `[n]P`, computed in extended coordinates (see the file header). -/
def nsmul (n : Nat) (P : Point) : Point := (Ext.nsmul n (Ext.ofPoint P)).toPoint

/-- Ed25519 has cofactor eight, so a point has small order exactly when
`[8]P` is the identity. -/
def smallOrder (P : Point) : Bool := nsmul 8 P = identity

/-- Canonical 32-byte encoding: `y` little-endian, sign of `x` in bit 255. -/
def encode (P : Point) : ByteArray :=
  natToLE (P.y.val + (if Fe.isNegative P.x then 2 ^ 255 else 0)) 32

/-- The permissive decoder used by Go's `crypto/ed25519`, curve25519-dalek
and Agave. Unlike RFC 8032 section 5.1.3 it accepts a noncanonical `y`
(values `p` to `2^255 - 1`, reduced modulo `p`) and accepts the sign bit set
on `x = 0` (the "negative zero" encodings). It rejects only wrong lengths and
`y` values with no curve point. -/
def decode (bytes : ByteArray) : Option Point :=
  if bytes.size ≠ 32 then none
  else
    let n := leNat bytes
    let y := Fe.ofNat (n % 2 ^ 255)
    let signBit := n / 2 ^ 255 = 1
    let yy := y * y
    match Fe.sqrtRatio (yy - 1) (d * yy + 1) with
    | none => none
    | some root =>
        let x := if Fe.isNegative root = signBit then root else -root
        some ⟨x, y⟩

/-- The standard basepoint, `y = 4/5` with `x` even. -/
def basepoint : Point :=
  ⟨Fe.ofNat 15112221349535400772501151409588531511454012693041857206046113283949847762202,
   Fe.ofNat 46316835694926478169428394003475163141307993866256225615783033603165251855960⟩

end Point
end NaryaSpec
