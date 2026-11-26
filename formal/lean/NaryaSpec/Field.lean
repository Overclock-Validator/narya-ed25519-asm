/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

The prime field GF(2^255 - 19) as canonical natural-number residues. Every
operation reduces with `%`, so `Fe` equality is equality of residues. There
are no limbs, carries or redundant representations here; relating Narya's
radix-2^51 limbs to these residues is the job of the leaf refinement proofs.
-/

namespace NaryaSpec

/-- The field prime `2^255 - 19`. -/
def p : Nat := 2 ^ 255 - 19

/-- A field element. Invariant: `val < p`. The only constructor used in this
specification is `Fe.ofNat`, which establishes it. -/
structure Fe where
  val : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Fe

def ofNat (n : Nat) : Fe := ⟨n % p⟩

instance (n : Nat) : OfNat Fe n := ⟨ofNat n⟩
instance : Add Fe := ⟨fun a b => ofNat (a.val + b.val)⟩
instance : Mul Fe := ⟨fun a b => ofNat (a.val * b.val)⟩
instance : Neg Fe := ⟨fun a => ofNat (p - a.val)⟩
instance : Sub Fe := ⟨fun a b => a + -b⟩

/-- `a ^ e` by binary exponentiation. -/
def pow (a : Fe) (e : Nat) : Fe :=
  if _h : e = 0 then 1
  else
    let half := pow (a * a) (e / 2)
    if e % 2 = 1 then a * half else half
termination_by e
decreasing_by omega

/-- Multiplicative inverse by Fermat's little theorem; `inv 0 = 0`. -/
def inv (a : Fe) : Fe := pow a (p - 2)

/-- RFC 8032 calls an element negative when its canonical value is odd. -/
def isNegative (a : Fe) : Bool := a.val % 2 = 1

/-- A square root of -1, `2^((p-1)/4)`. -/
def sqrtM1 : Fe := pow 2 ((p - 1) / 4)

/-- A square root of `u / v` when one exists, by RFC 8032 section 5.1.3
step 3 (`p ≡ 5 mod 8`). The root's sign is unspecified; callers fix it. -/
def sqrtRatio (u v : Fe) : Option Fe :=
  let ratio := u * inv v
  let candidate := pow ratio ((p + 3) / 8)
  if candidate * candidate = ratio then some candidate
  else if candidate * candidate = -ratio then some (candidate * sqrtM1)
  else none

end Fe
end NaryaSpec
