/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Source-level refinement of the r51 x8 add, subtract, and negate assembly
leaves. GeneratedR51LinearTrace is extracted from the exact assembly source;
this file proves the corresponding modular semantics, unsigned no-wrap, and
composable-u52 output contract for one lane. It does not decode the emitted
object or model the x86 ISA and System V boundary.
-/

import NaryaFormal.GeneratedR51LinearTrace

namespace NaryaFormal.Radix51.LinearTrace

open NaryaFormal.Radix51.GeneratedR51LinearTrace

def Composable (x : Loose5) : Prop :=
  x.l0 < U52 ∧ x.l1 < U52 ∧ x.l2 < U52 ∧ x.l3 < U52 ∧ x.l4 < U52

theorem source_constants_correct :
    sourceMask = B - 1 ∧ sourceFold = 19 ∧
      sourceBias0 = 4 * (B - 19) ∧ sourceBiasN = 4 * (B - 1) := by
  norm_num [sourceMask, sourceFold, sourceBias0, sourceBiasN, B]

theorem source_bias_value :
    sourceBias0 + sourceBiasN * B + sourceBiasN * B ^ 2 +
      sourceBiasN * B ^ 3 + sourceBiasN * B ^ 4 = 4 * P := by
  norm_num [sourceBias0, sourceBiasN, B, P]

theorem add_raw_value (x y : Loose5) :
    looseValue (addRaw x y) = looseValue x + looseValue y := by
  simp [addRaw, looseValue]
  ring

theorem add_raw_u64 (x y : Loose5) (hx : Composable x) (hy : Composable y) :
    (addRaw x y).l0 < 2 ^ 64 ∧ (addRaw x y).l1 < 2 ^ 64 ∧
      (addRaw x y).l2 < 2 ^ 64 ∧ (addRaw x y).l3 < 2 ^ 64 ∧
      (addRaw x y).l4 < 2 ^ 64 := by
  rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3, hy4⟩
  simp only [addRaw]
  norm_num [U52] at hx0 hx1 hx2 hx3 hx4 hy0 hy1 hy2 hy3 hy4 ⊢
  omega

theorem sub_inputs_covered (x y : Loose5) (hx : Composable x)
    (hy : Composable y) :
    y.l0 ≤ x.l0 + sourceBias0 ∧ y.l1 ≤ x.l1 + sourceBiasN ∧
      y.l2 ≤ x.l2 + sourceBiasN ∧ y.l3 ≤ x.l3 + sourceBiasN ∧
      y.l4 ≤ x.l4 + sourceBiasN := by
  rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3, hy4⟩
  norm_num [sourceBias0, sourceBiasN, U52] at *
  omega

theorem sub_raw_value (x y : Loose5) (hx : Composable x)
    (hy : Composable y) :
    looseValue (subRaw x y) + looseValue y = looseValue x + 4 * P := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := sub_inputs_covered x y hx hy
  simp only [subRaw, looseValue]
  norm_num [sourceBias0, sourceBiasN, B, P] at h0 h1 h2 h3 h4 ⊢
  omega

theorem sub_raw_u64 (x y : Loose5) (hx : Composable x) (hy : Composable y) :
    (subRaw x y).l0 < 2 ^ 64 ∧ (subRaw x y).l1 < 2 ^ 64 ∧
      (subRaw x y).l2 < 2 ^ 64 ∧ (subRaw x y).l3 < 2 ^ 64 ∧
      (subRaw x y).l4 < 2 ^ 64 := by
  rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3, hy4⟩
  simp only [subRaw]
  norm_num [sourceBias0, sourceBiasN, U52] at *
  omega

theorem neg_inputs_covered (x : Loose5) (hx : Composable x) :
    x.l0 ≤ sourceBias0 ∧ x.l1 ≤ sourceBiasN ∧ x.l2 ≤ sourceBiasN ∧
      x.l3 ≤ sourceBiasN ∧ x.l4 ≤ sourceBiasN := by
  rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
  norm_num [sourceBias0, sourceBiasN, U52] at *
  omega

theorem neg_raw_value (x : Loose5) (hx : Composable x) :
    looseValue (negRaw x) + looseValue x = 4 * P := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := neg_inputs_covered x hx
  simp only [negRaw, looseValue]
  norm_num [sourceBias0, sourceBiasN, B, P] at h0 h1 h2 h3 h4 ⊢
  omega

theorem neg_raw_u64 (x : Loose5) (hx : Composable x) :
    (negRaw x).l0 < 2 ^ 64 ∧ (negRaw x).l1 < 2 ^ 64 ∧
      (negRaw x).l2 < 2 ^ 64 ∧ (negRaw x).l3 < 2 ^ 64 ∧
      (negRaw x).l4 < 2 ^ 64 := by
  rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
  simp only [negRaw]
  norm_num [sourceBias0, sourceBiasN, U52] at *
  omega

theorem add_assembly_trace_correct (x y : Loose5)
    (hx : Composable x) (hy : Composable y) :
    looseValue (addOutput x y) % P =
        (looseValue x + looseValue y) % P ∧ Composable (addOutput x y) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := add_raw_u64 x y hx hy
  constructor
  · calc
      looseValue (addOutput x y) % P = looseValue (addRaw x y) % P :=
        parallel_carry_preserves_mod (addRaw x y)
      _ = (looseValue x + looseValue y) % P := by rw [add_raw_value]
  · exact normalized_limbs_u52_of_u64 (addRaw x y) h0 h1 h2 h3 h4

theorem sub_assembly_trace_correct (x y : Loose5)
    (hx : Composable x) (hy : Composable y) :
    (looseValue (subOutput x y) + looseValue y) % P =
        looseValue x % P ∧ Composable (subOutput x y) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := sub_raw_u64 x y hx hy
  constructor
  · calc
      (looseValue (subOutput x y) + looseValue y) % P =
          (looseValue (subOutput x y) % P + looseValue y % P) % P :=
            Nat.add_mod _ _ _
      _ = (looseValue (subRaw x y) % P + looseValue y % P) % P := by
        rw [subOutput, parallel_carry_preserves_mod (subRaw x y)]
      _ = (looseValue (subRaw x y) + looseValue y) % P :=
        (Nat.add_mod _ _ _).symm
      _ = (looseValue x + 4 * P) % P := by rw [sub_raw_value x y hx hy]
      _ = looseValue x % P := by simp [Nat.add_mod]
  · exact normalized_limbs_u52_of_u64 (subRaw x y) h0 h1 h2 h3 h4

theorem neg_assembly_trace_correct (x : Loose5) (hx : Composable x) :
    (looseValue (negOutput x) + looseValue x) % P = 0 ∧
      Composable (negOutput x) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := neg_raw_u64 x hx
  constructor
  · calc
      (looseValue (negOutput x) + looseValue x) % P =
          (looseValue (negOutput x) % P + looseValue x % P) % P :=
            Nat.add_mod _ _ _
      _ = (looseValue (negRaw x) % P + looseValue x % P) % P := by
        rw [negOutput, parallel_carry_preserves_mod (negRaw x)]
      _ = (looseValue (negRaw x) + looseValue x) % P :=
        (Nat.add_mod _ _ _).symm
      _ = (4 * P) % P := by rw [neg_raw_value x hx]
      _ = 0 := by simp
  · exact normalized_limbs_u52_of_u64 (negRaw x) h0 h1 h2 h3 h4

end NaryaFormal.Radix51.LinearTrace
