/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Algebraic core of the signed radix-2^21 scalar reducer. The source-level
per-instruction range certificate lives in tools/check_scalar_reduce_bounds.py;
this file machine-checks the fold identity and the relational carry facts that
the interval transfer relies on.
-/

import Mathlib

namespace NaryaFormal.ScalarReduction

def B : ℤ := 2 ^ 21
def HalfB : ℤ := 2 ^ 20
def L : ℤ := 2 ^ 252 + 27742317777372353535851937790883648493

def FoldPolynomial : ℤ :=
  666643 + 470296 * B + 654183 * B ^ 2 - 997805 * B ^ 3 +
    136657 * B ^ 4 - 683901 * B ^ 5

/-- The six ref10 constants represent the negative low part of the group
order, as an exact integer identity rather than only a congruence. -/
theorem fold_polynomial_exact :
    FoldPolynomial = -(L - 2 ^ 252) := by
  norm_num [FoldPolynomial, B, L]

/-- Since `B^12 = 2^252`, replacing a coefficient at position 12 with the
six signed constants changes the represented integer by exactly one `L`. -/
theorem radix12_eq_order_add_fold : B ^ 12 = L + FoldPolynomial := by
  norm_num [FoldPolynomial, B, L]

theorem radix12_fold_mod_order : B ^ 12 ≡ FoldPolynomial [ZMOD L] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  rw [radix12_eq_order_add_fold]
  ring

def ordinaryQuotient (x : ℤ) : ℤ := x / B
def ordinaryResidual (x : ℤ) : ℤ := x - ordinaryQuotient x * B

def centeredQuotient (x : ℤ) : ℤ := (x + HalfB) / B
def centeredResidual (x : ℤ) : ℤ := x - centeredQuotient x * B

theorem ordinary_residual_eq_emod (x : ℤ) : ordinaryResidual x = x % B := by
  have decomposition := Int.emod_add_ediv x B
  calc
    ordinaryResidual x = x - (x / B) * B := rfl
    _ = x - B * (x / B) := by rw [mul_comm]
    _ = x % B := by omega

theorem ordinary_carry_bounds (x : ℤ) :
    0 ≤ ordinaryResidual x ∧ ordinaryResidual x < B := by
  rw [ordinary_residual_eq_emod]
  exact ⟨Int.emod_nonneg x (by norm_num [B]),
    Int.emod_lt_of_pos x (by norm_num [B])⟩

theorem centered_residual_eq_emod (x : ℤ) :
    centeredResidual x = (x + HalfB) % B - HalfB := by
  have decomposition := Int.emod_add_ediv (x + HalfB) B
  calc
    centeredResidual x = x - ((x + HalfB) / B) * B := rfl
    _ = x - B * ((x + HalfB) / B) := by rw [mul_comm]
    _ = (x + HalfB) % B - HalfB := by omega

theorem centered_carry_bounds (x : ℤ) :
    -HalfB ≤ centeredResidual x ∧ centeredResidual x < HalfB := by
  rw [centered_residual_eq_emod]
  have hb0 : B ≠ 0 := by norm_num [B]
  have hbpos : 0 < B := by norm_num [B]
  have hdouble : B = 2 * HalfB := by norm_num [B, HalfB]
  have nonnegative := Int.emod_nonneg (x + HalfB) hb0
  have below := Int.emod_lt_of_pos (x + HalfB) hbpos
  constructor <;> omega

theorem ordinary_carry_decomposes (x : ℤ) :
    x = ordinaryResidual x + ordinaryQuotient x * B := by
  simp only [ordinaryResidual]
  ring

theorem centered_carry_decomposes (x : ℤ) :
    x = centeredResidual x + centeredQuotient x * B := by
  simp only [centeredResidual]
  ring

/-- Moving any quotient from coefficient `i` to `i+1` preserves the exact
represented integer. This theorem is independent of how the quotient was
chosen; the two carry-bound theorems supply the normal-form ranges. -/
theorem adjacent_carry_preserves
    (x next quotient : ℤ) (position : ℕ) :
    (x - quotient * B) * B ^ position +
        (next + quotient) * B ^ (position + 1) =
      x * B ^ position + next * B ^ (position + 1) := by
  rw [pow_succ]
  ring

end NaryaFormal.ScalarReduction
