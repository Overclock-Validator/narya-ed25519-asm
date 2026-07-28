/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Algebraic and range foundations for Narya's five-limb radix-2^51 IFMA field
kernel. This file deliberately does not model x86 instructions, registers,
memory, or the eight-lane wrapper. Those are separate refinement layers.
-/

import Mathlib

namespace NaryaFormal.Radix51

/-! ## Representation constants -/

def B : ℕ := 2 ^ 51
def U52 : ℕ := 2 ^ 52
def P : ℕ := 2 ^ 255 - 19

theorem B_pos : 0 < B := by
  norm_num [B]

theorem U52_pos : 0 < U52 := by
  norm_num [U52]

theorem P_pos : 0 < P := by
  norm_num [P]

theorem U52_eq_two_mul_B : U52 = 2 * B := by
  norm_num [U52, B]

theorem B_pow_five : B ^ 5 = P + 19 := by
  norm_num [B, P]

/-! ## Scalar semantics of one IFMA product pair -/

def lo52 (x y : ℕ) : ℕ := (x * y) % U52
def hi52 (x y : ℕ) : ℕ := (x * y) / U52

theorem ifma_split_exact (x y : ℕ) :
    lo52 x y + U52 * hi52 x y = x * y := by
  simpa [lo52, hi52] using Nat.mod_add_div (x * y) U52

theorem ifma_split_radix51 (x y : ℕ) :
    lo52 x y + B * (2 * hi52 x y) = x * y := by
  calc
    lo52 x y + B * (2 * hi52 x y) =
        lo52 x y + U52 * hi52 x y := by
          rw [U52_eq_two_mul_B]
          ring
    _ = x * y := ifma_split_exact x y

theorem lo52_lt (x y : ℕ) : lo52 x y < U52 := by
  exact Nat.mod_lt _ U52_pos

theorem hi52_lt_of_u52 {x y : ℕ} (hx : x < U52) (hy : y < U52) :
    hi52 x y < U52 := by
  rw [hi52, Nat.div_lt_iff_lt_mul U52_pos]
  nlinarith

/-! ## Positioning and the 2^255 = 19 fold -/

theorem positioned_ifma_split_exact (x y degree : ℕ) :
    x * y * B ^ degree =
      lo52 x y * B ^ degree +
        (2 * hi52 x y) * B ^ (degree + 1) := by
  rw [← ifma_split_radix51 x y]
  ring

abbrev FiveLimbs := Fin 5 → ℕ

def radixValue (x : FiveLimbs) : ℕ :=
  ∑ i : Fin 5, x i * B ^ i.val

def splitConvolution (x y : FiveLimbs) : ℕ :=
  ∑ i : Fin 5, ∑ j : Fin 5,
    (lo52 (x i) (y j) * B ^ (i.val + j.val) +
      (2 * hi52 (x i) (y j)) * B ^ (i.val + j.val + 1))

theorem split_convolution_exact (x y : FiveLimbs) :
    splitConvolution x y = radixValue x * radixValue y := by
  calc
    splitConvolution x y =
        ∑ i : Fin 5, ∑ j : Fin 5,
          x i * y j * B ^ (i.val + j.val) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact (positioned_ifma_split_exact
              (x i) (y j) (i.val + j.val)).symm
    _ = radixValue x * radixValue y := by
      rw [radixValue, radixValue, Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring

theorem fold_monomial_mod (coefficient degree : ℕ) :
    (coefficient * B ^ (degree + 5)) % P =
      (19 * coefficient * B ^ degree) % P := by
  rw [show B ^ (degree + 5) = B ^ degree * B ^ 5 by
    rw [pow_add]]
  rw [B_pow_five]
  rw [show coefficient * (B ^ degree * (P + 19)) =
      (coefficient * B ^ degree) * P + 19 * coefficient * B ^ degree by
    ring]
  simp

/-! ## Carry semantics -/

def carry (x : ℕ) : ℕ := x / B
def remainder (x : ℕ) : ℕ := x % B

theorem carry_decomposition (x : ℕ) :
    remainder x + B * carry x = x := by
  simpa [remainder, carry] using Nat.mod_add_div x B

theorem carry_step_preserves_value (x next : ℕ) :
    remainder x + B * (next + carry x) = x + B * next := by
  calc
    remainder x + B * (next + carry x) =
        (remainder x + B * carry x) + B * next := by ring
    _ = x + B * next := by rw [carry_decomposition]

theorem remainder_lt_B (x : ℕ) : remainder x < B := by
  exact Nat.mod_lt _ B_pos

structure Loose5 where
  l0 : ℕ
  l1 : ℕ
  l2 : ℕ
  l3 : ℕ
  l4 : ℕ
deriving Repr, DecidableEq

def looseValue (x : Loose5) : ℕ :=
  x.l0 + x.l1 * B + x.l2 * B ^ 2 + x.l3 * B ^ 3 + x.l4 * B ^ 4

def normalized (x : Loose5) : Loose5 :=
  { l0 := remainder x.l0 + 19 * carry x.l4
    l1 := remainder x.l1 + carry x.l0
    l2 := remainder x.l2 + carry x.l1
    l3 := remainder x.l3 + carry x.l2
    l4 := remainder x.l4 + carry x.l3 }

def carryCommon (x : Loose5) : ℕ :=
  remainder x.l0 + remainder x.l1 * B + remainder x.l2 * B ^ 2 +
    remainder x.l3 * B ^ 3 + remainder x.l4 * B ^ 4 +
    carry x.l0 * B + carry x.l1 * B ^ 2 + carry x.l2 * B ^ 3 +
    carry x.l3 * B ^ 4

theorem loose_value_decomposition (x : Loose5) :
    looseValue x = carryCommon x + carry x.l4 * B ^ 5 := by
  conv_lhs =>
    simp only [looseValue]
    rw [← carry_decomposition x.l0, ← carry_decomposition x.l1,
      ← carry_decomposition x.l2, ← carry_decomposition x.l3,
      ← carry_decomposition x.l4]
  simp only [carryCommon]
  ring

theorem normalized_value_decomposition (x : Loose5) :
    looseValue (normalized x) = carryCommon x + 19 * carry x.l4 := by
  simp only [looseValue, normalized, carryCommon]
  ring

theorem parallel_carry_preserves_mod (x : Loose5) :
    looseValue (normalized x) % P = looseValue x % P := by
  rw [normalized_value_decomposition, loose_value_decomposition]
  have hfold : (carry x.l4 * B ^ 5) % P =
      (19 * carry x.l4) % P := by
    simpa using fold_monomial_mod (carry x.l4) 0
  calc
    (carryCommon x + 19 * carry x.l4) % P =
        (carryCommon x % P + (19 * carry x.l4) % P) % P :=
          Nat.add_mod _ _ _
    _ = (carryCommon x % P + (carry x.l4 * B ^ 5) % P) % P := by
      rw [hfold]
    _ = (carryCommon x + carry x.l4 * B ^ 5) % P :=
      (Nat.add_mod _ _ _).symm

/-! ## Bounds used by the assembly schedule -/

theorem low_accumulator_five_terms_u64
    {a b c d e : ℕ}
    (ha : a < U52) (hb : b < U52) (hc : c < U52)
    (hd : d < U52) (he : e < U52) :
    a + b + c + d + e < 2 ^ 55 := by
  norm_num [U52] at *
  omega

theorem combined_degree_bound
    {low high lowCount highCount : ℕ}
    (hlow : low < lowCount * U52)
    (hhigh : high < highCount * U52) :
    low + 2 * high < (lowCount + 2 * highCount) * U52 := by
  nlinarith

theorem folded_limb0_bound {d0 d5 : ℕ}
    (h0 : d0 < U52) (h5 : d5 < 14 * U52) :
    d0 + 19 * d5 < 267 * U52 := by
  omega

theorem folded_limb1_bound {d1 d6 : ℕ}
    (h1 : d1 < 4 * U52) (h6 : d6 < 11 * U52) :
    d1 + 19 * d6 < 213 * U52 := by
  omega

theorem folded_limb2_bound {d2 d7 : ℕ}
    (h2 : d2 < 7 * U52) (h7 : d7 < 8 * U52) :
    d2 + 19 * d7 < 159 * U52 := by
  omega

theorem folded_limb3_bound {d3 d8 : ℕ}
    (h3 : d3 < 10 * U52) (h8 : d8 < 5 * U52) :
    d3 + 19 * d8 < 105 * U52 := by
  omega

theorem folded_limb4_bound {d4 d9 : ℕ}
    (h4 : d4 < 13 * U52) (h9 : d9 < 2 * U52) :
    d4 + 19 * d9 < 51 * U52 := by
  omega

def foldDegrees
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : ℕ) : Loose5 :=
  { l0 := d0 + 19 * d5
    l1 := d1 + 19 * d6
    l2 := d2 + 19 * d7
    l3 := d3 + 19 * d8
    l4 := d4 + 19 * d9 }

theorem folded_limb_u61_of_bound {t multiplier : ℕ}
    (hmultiplier : multiplier ≤ 267)
    (ht : t < multiplier * U52) :
    t < 2 ^ 61 := by
  calc
    t < multiplier * U52 := ht
    _ ≤ 267 * U52 := Nat.mul_le_mul_right U52 hmultiplier
    _ < 2 ^ 61 := by norm_num [U52]

theorem folded_degrees_u61
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : ℕ}
    (h0 : d0 < U52) (h1 : d1 < 4 * U52)
    (h2 : d2 < 7 * U52) (h3 : d3 < 10 * U52)
    (h4 : d4 < 13 * U52) (h5 : d5 < 14 * U52)
    (h6 : d6 < 11 * U52) (h7 : d7 < 8 * U52)
    (h8 : d8 < 5 * U52) (h9 : d9 < 2 * U52) :
    (foldDegrees d0 d1 d2 d3 d4 d5 d6 d7 d8 d9).l0 < 2 ^ 61 ∧
      (foldDegrees d0 d1 d2 d3 d4 d5 d6 d7 d8 d9).l1 < 2 ^ 61 ∧
      (foldDegrees d0 d1 d2 d3 d4 d5 d6 d7 d8 d9).l2 < 2 ^ 61 ∧
      (foldDegrees d0 d1 d2 d3 d4 d5 d6 d7 d8 d9).l3 < 2 ^ 61 ∧
      (foldDegrees d0 d1 d2 d3 d4 d5 d6 d7 d8 d9).l4 < 2 ^ 61 := by
  constructor
  · exact folded_limb_u61_of_bound (by norm_num)
      (folded_limb0_bound h0 h5)
  constructor
  · exact folded_limb_u61_of_bound (by norm_num)
      (folded_limb1_bound h1 h6)
  constructor
  · exact folded_limb_u61_of_bound (by norm_num)
      (folded_limb2_bound h2 h7)
  constructor
  · exact folded_limb_u61_of_bound (by norm_num)
      (folded_limb3_bound h3 h8)
  · exact folded_limb_u61_of_bound (by norm_num)
      (folded_limb4_bound h4 h9)

theorem carry_lt_1024_of_u61 {t : ℕ} (ht : t < 2 ^ 61) :
    carry t < 2 ^ 10 := by
  simp only [carry, B]
  omega

theorem carry_fold_output0_u52 {t0 t4 : ℕ}
    (ht4 : t4 < 2 ^ 61) :
    remainder t0 + 19 * carry t4 < U52 := by
  have hr := remainder_lt_B t0
  have hc := carry_lt_1024_of_u61 ht4
  norm_num [B, U52] at hr hc ⊢
  omega

theorem carry_output_u52 {current previous : ℕ}
    (hprevious : previous < 2 ^ 61) :
    remainder current + carry previous < U52 := by
  have hr := remainder_lt_B current
  have hc := carry_lt_1024_of_u61 hprevious
  norm_num [B, U52] at hr hc ⊢
  omega

theorem normalized_limbs_u52 (x : Loose5)
    (h0 : x.l0 < 2 ^ 61) (h1 : x.l1 < 2 ^ 61)
    (h2 : x.l2 < 2 ^ 61) (h3 : x.l3 < 2 ^ 61)
    (h4 : x.l4 < 2 ^ 61) :
    (normalized x).l0 < U52 ∧ (normalized x).l1 < U52 ∧
      (normalized x).l2 < U52 ∧ (normalized x).l3 < U52 ∧
      (normalized x).l4 < U52 := by
  constructor
  · exact carry_fold_output0_u52 h4
  constructor
  · exact carry_output_u52 h0
  constructor
  · exact carry_output_u52 h1
  constructor
  · exact carry_output_u52 h2
  · exact carry_output_u52 h3

/-!
`radix51_mul_correct_of_folded_schedule` is the algebraic composition seam.
The remaining implementation-refinement theorem must show that the assembly's
grouped low/high accumulators and five folds produce a `raw` value satisfying
`hfold`. It must establish the five u61 hypotheses instruction by instruction.
-/
theorem radix51_mul_correct_of_folded_schedule
    (x y : FiveLimbs) (raw : Loose5)
    (hfold : looseValue raw % P = splitConvolution x y % P)
    (h0 : raw.l0 < 2 ^ 61) (h1 : raw.l1 < 2 ^ 61)
    (h2 : raw.l2 < 2 ^ 61) (h3 : raw.l3 < 2 ^ 61)
    (h4 : raw.l4 < 2 ^ 61) :
    looseValue (normalized raw) % P =
        (radixValue x * radixValue y) % P ∧
      (normalized raw).l0 < U52 ∧ (normalized raw).l1 < U52 ∧
      (normalized raw).l2 < U52 ∧ (normalized raw).l3 < U52 ∧
      (normalized raw).l4 < U52 := by
  constructor
  · calc
      looseValue (normalized raw) % P = looseValue raw % P :=
        parallel_carry_preserves_mod raw
      _ = splitConvolution x y % P := hfold
      _ = (radixValue x * radixValue y) % P := by
        rw [split_convolution_exact]
  · exact normalized_limbs_u52 raw h0 h1 h2 h3 h4

end NaryaFormal.Radix51
