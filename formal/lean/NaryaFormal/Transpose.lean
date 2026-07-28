/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Pure lane model for the two YMM shuffle networks used by
`projective_niels_transpose_x8.S` and `affine_niels_transpose_x8.S`.

This file proves the representation change, not instruction decoding or the
System V memory trace. `tools/check_transpose_schedule.py` is the deliberately
small source bridge: it interprets the actual assembly macro and checks every
load/store invocation against the layouts modeled here.
-/

namespace NaryaFormal.Transpose

universe u

variable {α : Type u}

/-- Four 64-bit lanes, modeled parametrically so the result is about positions
rather than arithmetic values. -/
structure Q4 (α : Type u) where
  q0 : α
  q1 : α
  q2 : α
  q3 : α
deriving DecidableEq, Repr

/-- Eight 64-bit lanes after joining the lower and upper YMM halves. -/
structure Q8 (α : Type u) where
  q0 : α
  q1 : α
  q2 : α
  q3 : α
  q4 : α
  q5 : α
  q6 : α
  q7 : α
deriving DecidableEq, Repr

/-- Four input rows or four transposed coordinate rows. -/
structure Rows4 (α : Type u) where
  r0 : Q4 α
  r1 : Q4 α
  r2 : Q4 α
  r3 : Q4 α
deriving DecidableEq, Repr

def unpackLowQword (a b : Q4 α) : Q4 α :=
  ⟨a.q0, b.q0, a.q2, b.q2⟩

def unpackHighQword (a b : Q4 α) : Q4 α :=
  ⟨a.q1, b.q1, a.q3, b.q3⟩

/-- EVEX.256 `VSHUFI64X2`: bit 0 selects the 128-bit half of the first
source for the low destination half; bit 1 selects the half of the second
source for the high destination half. Higher immediate bits are ignored at
this vector length. -/
def shuffleI64x2Ymm (imm : Nat) (a b : Q4 α) : Q4 α :=
  let alo := if imm.testBit 0 then (a.q2, a.q3) else (a.q0, a.q1)
  let bhi := if imm.testBit 1 then (b.q2, b.q3) else (b.q0, b.q1)
  ⟨alo.1, alo.2, bhi.1, bhi.2⟩

/-- The instruction sequence in each assembly file's `TRANSPOSE_4X4` macro. -/
def transpose4Schedule (input : Rows4 α) : Rows4 α :=
  let t0 := unpackLowQword input.r0 input.r1
  let t1 := unpackHighQword input.r0 input.r1
  let t2 := unpackLowQword input.r2 input.r3
  let t3 := unpackHighQword input.r2 input.r3
  ⟨shuffleI64x2Ymm 0 t0 t2,
   shuffleI64x2Ymm 0 t1 t3,
   shuffleI64x2Ymm 3 t0 t2,
   shuffleI64x2Ymm 3 t1 t3⟩

/-- The desired mathematical 4×4 transpose. -/
def transpose4Spec (input : Rows4 α) : Rows4 α :=
  ⟨⟨input.r0.q0, input.r1.q0, input.r2.q0, input.r3.q0⟩,
   ⟨input.r0.q1, input.r1.q1, input.r2.q1, input.r3.q1⟩,
   ⟨input.r0.q2, input.r1.q2, input.r2.q2, input.r3.q2⟩,
   ⟨input.r0.q3, input.r1.q3, input.r2.q3, input.r3.q3⟩⟩

theorem transpose4_schedule_exact (input : Rows4 α) :
    transpose4Schedule input = transpose4Spec input := by
  cases input with
  | mk r0 r1 r2 r3 =>
      cases r0
      cases r1
      cases r2
      cases r3
      rfl

def joinHalves (low high : Q4 α) : Q8 α :=
  ⟨low.q0, low.q1, low.q2, low.q3,
   high.q0, high.q1, high.q2, high.q3⟩

/-- One selected projective-Niels entry in the micro-AoS source layout. -/
structure ProjectiveEntry (α : Type u) where
  yPlusX : α
  yMinusX : α
  z : α
  t2d : α
deriving DecidableEq, Repr

/-- One limb row of the arithmetic-SoA projective-Niels output. -/
structure ProjectiveRowX8 (α : Type u) where
  yPlusX : Q8 α
  yMinusX : Q8 α
  z : Q8 α
  t2d : Q8 α
deriving DecidableEq, Repr

def projectiveRows4 (a b c d : ProjectiveEntry α) : Rows4 α :=
  ⟨⟨a.yPlusX, a.yMinusX, a.z, a.t2d⟩,
   ⟨b.yPlusX, b.yMinusX, b.z, b.t2d⟩,
   ⟨c.yPlusX, c.yMinusX, c.z, c.t2d⟩,
   ⟨d.yPlusX, d.yMinusX, d.z, d.t2d⟩⟩

/-- The two-half x8 projective transpose performed independently for every
one of the five radix-51 limbs. -/
def projectiveTransposeRowX8
    (e0 e1 e2 e3 e4 e5 e6 e7 : ProjectiveEntry α) : ProjectiveRowX8 α :=
  let low := transpose4Schedule (projectiveRows4 e0 e1 e2 e3)
  let high := transpose4Schedule (projectiveRows4 e4 e5 e6 e7)
  ⟨joinHalves low.r0 high.r0,
   joinHalves low.r1 high.r1,
   joinHalves low.r2 high.r2,
   joinHalves low.r3 high.r3⟩

def projectiveTransposeSpecX8
    (e0 e1 e2 e3 e4 e5 e6 e7 : ProjectiveEntry α) : ProjectiveRowX8 α :=
  ⟨⟨e0.yPlusX, e1.yPlusX, e2.yPlusX, e3.yPlusX,
     e4.yPlusX, e5.yPlusX, e6.yPlusX, e7.yPlusX⟩,
   ⟨e0.yMinusX, e1.yMinusX, e2.yMinusX, e3.yMinusX,
     e4.yMinusX, e5.yMinusX, e6.yMinusX, e7.yMinusX⟩,
   ⟨e0.z, e1.z, e2.z, e3.z, e4.z, e5.z, e6.z, e7.z⟩,
   ⟨e0.t2d, e1.t2d, e2.t2d, e3.t2d,
     e4.t2d, e5.t2d, e6.t2d, e7.t2d⟩⟩

theorem projective_transpose_x8_lane_exact
    (e0 e1 e2 e3 e4 e5 e6 e7 : ProjectiveEntry α) :
    projectiveTransposeRowX8 e0 e1 e2 e3 e4 e5 e6 e7 =
      projectiveTransposeSpecX8 e0 e1 e2 e3 e4 e5 e6 e7 := by
  cases e0
  cases e1
  cases e2
  cases e3
  cases e4
  cases e5
  cases e6
  cases e7
  rfl

/-- One selected affine-Niels entry. The assembly's `k1 = 0b0111` masked
load appends a zero fourth qword before applying the same 4×4 network. -/
structure AffineEntry (α : Type u) where
  yPlusX : α
  yMinusX : α
  t2d : α
deriving DecidableEq, Repr

structure AffineRowX8 (α : Type u) where
  yPlusX : Q8 α
  yMinusX : Q8 α
  t2d : Q8 α
deriving DecidableEq, Repr

def affineRows4 [Zero α] (a b c d : AffineEntry α) : Rows4 α :=
  ⟨⟨a.yPlusX, a.yMinusX, a.t2d, 0⟩,
   ⟨b.yPlusX, b.yMinusX, b.t2d, 0⟩,
   ⟨c.yPlusX, c.yMinusX, c.t2d, 0⟩,
   ⟨d.yPlusX, d.yMinusX, d.t2d, 0⟩⟩

def affineTransposeRowX8 [Zero α]
    (e0 e1 e2 e3 e4 e5 e6 e7 : AffineEntry α) : AffineRowX8 α :=
  let low := transpose4Schedule (affineRows4 e0 e1 e2 e3)
  let high := transpose4Schedule (affineRows4 e4 e5 e6 e7)
  ⟨joinHalves low.r0 high.r0,
   joinHalves low.r1 high.r1,
   joinHalves low.r2 high.r2⟩

def affineTransposeSpecX8
    (e0 e1 e2 e3 e4 e5 e6 e7 : AffineEntry α) : AffineRowX8 α :=
  ⟨⟨e0.yPlusX, e1.yPlusX, e2.yPlusX, e3.yPlusX,
     e4.yPlusX, e5.yPlusX, e6.yPlusX, e7.yPlusX⟩,
   ⟨e0.yMinusX, e1.yMinusX, e2.yMinusX, e3.yMinusX,
     e4.yMinusX, e5.yMinusX, e6.yMinusX, e7.yMinusX⟩,
   ⟨e0.t2d, e1.t2d, e2.t2d, e3.t2d,
     e4.t2d, e5.t2d, e6.t2d, e7.t2d⟩⟩

theorem affine_transpose_x8_lane_exact [Zero α]
    (e0 e1 e2 e3 e4 e5 e6 e7 : AffineEntry α) :
    affineTransposeRowX8 e0 e1 e2 e3 e4 e5 e6 e7 =
      affineTransposeSpecX8 e0 e1 e2 e3 e4 e5 e6 e7 := by
  cases e0
  cases e1
  cases e2
  cases e3
  cases e4
  cases e5
  cases e6
  cases e7
  rfl

end NaryaFormal.Transpose
