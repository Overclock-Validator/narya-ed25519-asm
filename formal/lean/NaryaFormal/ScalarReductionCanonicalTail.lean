/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Canonical-tail lemmas for Narya's signed radix-2^21 scalar reducer.

This file contains no proof escapes or custom axioms. The per-limb hypotheses
in `first_final_fold_value_bounds` are the inclusive source-certificate
intervals immediately after the first final FOLD of limb 12 and before the
first ordinary carry pass.
-/

import NaryaFormal.ScalarReduction

namespace NaryaFormal.ScalarReduction

def radix12Value
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : ℤ) : ℤ :=
  s0 +
    s1 * B +
    s2 * B ^ 2 +
    s3 * B ^ 3 +
    s4 * B ^ 4 +
    s5 * B ^ 5 +
    s6 * B ^ 6 +
    s7 * B ^ 7 +
    s8 * B ^ 8 +
    s9 * B ^ 9 +
    s10 * B ^ 10 +
    s11 * B ^ 11

/-- Exact change in the represented integer made by one complete FOLD macro.
If the consumed coefficient is at position `position + 12`, the macro changes
the integer by `-high * L * B^position`, hence preserves it modulo `L`. -/
theorem fold_at_exact_delta (high : ℤ) (position : ℕ) :
    high * FoldPolynomial * B ^ position -
        high * B ^ (position + 12) =
      -high * L * B ^ position := by
  rw [pow_add, radix12_eq_order_add_fold]
  ring

theorem fold_at_mod_order (high : ℤ) (position : ℕ) :
    high * B ^ (position + 12) ≡
      high * FoldPolynomial * B ^ position [ZMOD L] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-high * B ^ position, ?_⟩
  rw [pow_add, radix12_eq_order_add_fold]
  ring

set_option maxHeartbeats 2000000 in
/-- Independent interval hull for the represented integer immediately after
the first final FOLD. These constants are generated from the exact source
schedule, not from final output limb widths. -/
theorem first_final_fold_value_bounds
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : ℤ)
    (h0l : -1715219 ≤ s0) (h0u : s0 ≤ 19714579)
    (h1l : -1518872 ≤ s1) (h1u : s1 ≤ 14216863)
    (h2l : -2648359 ≤ s2) (h2u : s2 ≤ 58488439)
    (h3l : -28987116 ≤ s3) (h3u : s3 ≤ 2046380)
    (h4l : -84755560 ≤ s4) (h4u : s4 ≤ 44656394)
    (h5l : -20197804 ≤ s5) (h5u : s5 ≤ 1732476)
    (h6l : -194138808 ≤ s6) (h6u : s6 ≤ 12380602)
    (h7l : -1048576 ≤ s7) (h7u : s7 ≤ 1048575)
    (h8l : -127875146 ≤ s8) (h8u : s8 ≤ 3485823)
    (h9l : -1048576 ≤ s9) (h9u : s9 ≤ 1048575)
    (h10l : -24207876 ≤ s10) (h10u : s10 ≤ 1750290)
    (h11l : -1048576 ≤ s11) (h11u : s11 ≤ 1048575) :
    -3618542622837234973757065234647689667302434163242247946257515452174326967315 ≤
        radix12Value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∧
      radix12Value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ≤
        3618502217903952098236647382353507627699791367870745868658338408809892729363 := by
  constructor
  · norm_num [radix12Value, B] at *
    omega
  · norm_num [radix12Value, B] at *
    omega

set_option maxHeartbeats 2000000 in
/-- The source-certified state before the first ordinary carry pass lies in one
signed radix-`B^12` window. This is the relational fact that final independent
limb intervals were missing. -/
theorem first_final_fold_value_abs_lt_radix12
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : ℤ)
    (h0l : -1715219 ≤ s0) (h0u : s0 ≤ 19714579)
    (h1l : -1518872 ≤ s1) (h1u : s1 ≤ 14216863)
    (h2l : -2648359 ≤ s2) (h2u : s2 ≤ 58488439)
    (h3l : -28987116 ≤ s3) (h3u : s3 ≤ 2046380)
    (h4l : -84755560 ≤ s4) (h4u : s4 ≤ 44656394)
    (h5l : -20197804 ≤ s5) (h5u : s5 ≤ 1732476)
    (h6l : -194138808 ≤ s6) (h6u : s6 ≤ 12380602)
    (h7l : -1048576 ≤ s7) (h7u : s7 ≤ 1048575)
    (h8l : -127875146 ≤ s8) (h8u : s8 ≤ 3485823)
    (h9l : -1048576 ≤ s9) (h9u : s9 ≤ 1048575)
    (h10l : -24207876 ≤ s10) (h10u : s10 ≤ 1750290)
    (h11l : -1048576 ≤ s11) (h11u : s11 ≤ 1048575) :
    -(B ^ 12) <
        radix12Value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∧
      radix12Value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 <
        B ^ 12 := by
  have h := first_final_fold_value_bounds
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    h0l h0u h1l h1u h2l h2u h3l h3u h4l h4u h5l h5u
    h6l h6u h7l h7u h8l h8u h9l h9u h10l h10u h11l h11u
  norm_num [B] at h ⊢
  omega

/-- If an ordinary carry chain decomposes a value from one signed radix window
as `low + top*B^12`, with the low twelve digits in `[0,B^12)`, then the only
possible top carry is `-1` or `0`. -/
theorem one_window_top_carry
    (value low top : ℤ)
    (hvalueLower : -(B ^ 12) < value)
    (hvalueUpper : value < B ^ 12)
    (hlowLower : 0 ≤ low)
    (hlowUpper : low < B ^ 12)
    (hdecompose : value = low + top * B ^ 12) :
    top = -1 ∨ top = 0 := by
  norm_num [B] at hvalueLower hvalueUpper hlowLower hlowUpper hdecompose ⊢
  omega

/-- The second FOLD is a conditional addition of `L`: top=0 leaves the positive
value alone, while top=-1 adds exactly `L`. Either branch is canonical. -/
theorem second_fold_makes_canonical
    (value low top : ℤ)
    (hvalueLower : -(B ^ 12) < value)
    (hvalueUpper : value < B ^ 12)
    (hlowLower : 0 ≤ low)
    (hlowUpper : low < B ^ 12)
    (hdecompose : value = low + top * B ^ 12) :
    0 ≤ low + top * FoldPolynomial ∧
      low + top * FoldPolynomial < L := by
  have htop := one_window_top_carry value low top
    hvalueLower hvalueUpper hlowLower hlowUpper hdecompose
  have hfold : FoldPolynomial = B ^ 12 - L := by
    have h := radix12_eq_order_add_fold
    omega
  rcases htop with htop | htop
  · subst top
    rw [hfold]
    norm_num [B, L] at hvalueLower hvalueUpper hlowLower hlowUpper hdecompose ⊢
    omega
  · subst top
    rw [hfold]
    norm_num [B, L] at hvalueLower hvalueUpper hlowLower hlowUpper hdecompose ⊢
    omega

/-- Canonical scalars may use bit 252. If a canonical value is split at
`B^11 = 2^231`, its top radix-2^21 coefficient can be exactly `B` but cannot
exceed it. -/
theorem canonical_top_limb_bound
    (value low top : ℤ)
    (hvalueLower : 0 ≤ value)
    (hvalueUpper : value < L)
    (hlowLower : 0 ≤ low)
    (hlowUpper : low < B ^ 11)
    (hdecompose : value = low + top * B ^ 11) :
    0 ≤ top ∧ top ≤ B := by
  norm_num [B, L] at hvalueLower hvalueUpper hlowLower hlowUpper hdecompose ⊢
  omega

/-- If bit 252 is present (`top = B`), canonicality forces the lower 252-bit
part below the low-order constant `L-B^12`. This is the exact condition needed
to serialize values in `[2^252,L)`, including `L-1`. -/
theorem canonical_top_eq_B_lower_part
    (value low top : ℤ)
    (hvalueLower : 0 ≤ value)
    (hvalueUpper : value < L)
    (hdecompose : value = low + top * B ^ 11)
    (htop : top = B) :
    low < L - B ^ 12 := by
  subst top
  norm_num [B, L] at hvalueLower hvalueUpper hdecompose ⊢
  omega

end NaryaFormal.ScalarReduction
