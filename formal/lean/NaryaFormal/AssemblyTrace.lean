/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Arithmetic trace model for `narya_r51x8_mul_ifma`. The product lists below
follow the assembly's row-major MUL_PAIR order. This layer proves arithmetic
grouping and machine-word bounds; it does not model registers, memory, CPUID,
or the System V ABI.
-/

import NaryaFormal.Radix51

namespace NaryaFormal.Radix51.AssemblyTrace

def lowTerms (x y : FiveLimbs) : ℕ → List ℕ
  | 0 => [lo52 (x 0) (y 0)]
  | 1 => [lo52 (x 0) (y 1), lo52 (x 1) (y 0)]
  | 2 => [lo52 (x 0) (y 2), lo52 (x 1) (y 1), lo52 (x 2) (y 0)]
  | 3 => [lo52 (x 0) (y 3), lo52 (x 1) (y 2), lo52 (x 2) (y 1),
      lo52 (x 3) (y 0)]
  | 4 => [lo52 (x 0) (y 4), lo52 (x 1) (y 3), lo52 (x 2) (y 2),
      lo52 (x 3) (y 1), lo52 (x 4) (y 0)]
  | 5 => [lo52 (x 1) (y 4), lo52 (x 2) (y 3), lo52 (x 3) (y 2),
      lo52 (x 4) (y 1)]
  | 6 => [lo52 (x 2) (y 4), lo52 (x 3) (y 3), lo52 (x 4) (y 2)]
  | 7 => [lo52 (x 3) (y 4), lo52 (x 4) (y 3)]
  | 8 => [lo52 (x 4) (y 4)]
  | _ => []

def highTerms (x y : FiveLimbs) : ℕ → List ℕ
  | 0 => [hi52 (x 0) (y 0)]
  | 1 => [hi52 (x 0) (y 1), hi52 (x 1) (y 0)]
  | 2 => [hi52 (x 0) (y 2), hi52 (x 1) (y 1), hi52 (x 2) (y 0)]
  | 3 => [hi52 (x 0) (y 3), hi52 (x 1) (y 2), hi52 (x 2) (y 1),
      hi52 (x 3) (y 0)]
  | 4 => [hi52 (x 0) (y 4), hi52 (x 1) (y 3), hi52 (x 2) (y 2),
      hi52 (x 3) (y 1), hi52 (x 4) (y 0)]
  | 5 => [hi52 (x 1) (y 4), hi52 (x 2) (y 3), hi52 (x 3) (y 2),
      hi52 (x 4) (y 1)]
  | 6 => [hi52 (x 2) (y 4), hi52 (x 3) (y 3), hi52 (x 4) (y 2)]
  | 7 => [hi52 (x 3) (y 4), hi52 (x 4) (y 3)]
  | 8 => [hi52 (x 4) (y 4)]
  | _ => []

/-!
`LimbsU52` is the actual source-operand contract of VPMADD52.  The lists above
are not merely a convenient convolution: their order is the order in which
the assembly updates each accumulator.  Bounds on every `take n` below are
therefore per-instruction prefix bounds, not just bounds on the final sum.
-/

def LimbsU52 (x : FiveLimbs) : Prop := ∀ i, x i < U52

def degreeCount (degree : ℕ) : ℕ :=
  if degree ≤ 4 then degree + 1
  else if degree < 9 then 9 - degree
  else 0

theorem low_terms_length (x y : FiveLimbs) {degree : ℕ} (hdegree : degree < 9) :
    (lowTerms x y degree).length = degreeCount degree := by
  interval_cases degree <;> rfl

theorem high_terms_length (x y : FiveLimbs) {degree : ℕ} (hdegree : degree < 9) :
    (highTerms x y degree).length = degreeCount degree := by
  interval_cases degree <;> rfl

theorem degree_count_pos {degree : ℕ} (hdegree : degree < 9) :
    0 < degreeCount degree := by
  interval_cases degree <;> norm_num [degreeCount]

theorem degree_count_le_five (degree : ℕ) : degreeCount degree ≤ 5 := by
  by_cases hlow : degree ≤ 4
  · rw [degreeCount, if_pos hlow]
    omega
  · rw [degreeCount, if_neg hlow]
    by_cases hhigh : degree < 9
    · rw [if_pos hhigh]
      omega
    · rw [if_neg hhigh]
      exact Nat.zero_le _

theorem low_term_lt_u52 (x y : FiveLimbs) {degree term : ℕ}
    (hdegree : degree < 9) (hterm : term ∈ lowTerms x y degree) :
    term < U52 := by
  have hxy (i j : Fin 5) : lo52 (x i) (y j) < U52 := lo52_lt _ _
  interval_cases degree <;> simp_all [lowTerms] <;> aesop

theorem high_term_lt_u52 (x y : FiveLimbs) (hx : LimbsU52 x) (hy : LimbsU52 y)
    {degree term : ℕ} (hdegree : degree < 9)
    (hterm : term ∈ highTerms x y degree) : term < U52 := by
  have hxy (i j : Fin 5) : hi52 (x i) (y j) < U52 :=
    hi52_lt_of_u52 (hx i) (hy j)
  interval_cases degree <;> simp_all [highTerms] <;> aesop

theorem list_sum_lt_length_mul_u52 {terms : List ℕ}
    (hne : terms ≠ []) (hterm : ∀ term ∈ terms, term < U52) :
    terms.sum < terms.length * U52 := by
  induction terms with
  | nil => exact (hne rfl).elim
  | cons head tail ih =>
      have hhead : head < U52 := hterm head (by simp)
      by_cases htail : tail = []
      · subst tail
        simpa using hhead
      · have htailBound : tail.sum < tail.length * U52 := by
          apply ih htail
          intro term hmem
          exact hterm term (by simp [hmem])
        simp only [List.sum_cons, List.length_cons]
        calc
          head + tail.sum < U52 + tail.length * U52 :=
            Nat.add_lt_add hhead htailBound
          _ = (tail.length + 1) * U52 := by ring

theorem prefix_sum_lt_five_u52 {terms : List ℕ} {count : ℕ}
    (hcountPos : 0 < count) (hcount : count ≤ terms.length)
    (hlength : terms.length ≤ 5)
    (hterm : ∀ term ∈ terms, term < U52) :
    (terms.take count).sum < 5 * U52 := by
  have htakeLength : (terms.take count).length = count :=
    List.length_take_of_le hcount
  have htakeNe : terms.take count ≠ [] := by
    intro hempty
    have := congrArg List.length hempty
    simp [htakeLength] at this
    omega
  have htakeTerm : ∀ term ∈ terms.take count, term < U52 := by
    intro term hmem
    exact hterm term (List.mem_of_mem_take hmem)
  have hsum := list_sum_lt_length_mul_u52 htakeNe htakeTerm
  rw [htakeLength] at hsum
  calc
    (terms.take count).sum < count * U52 := hsum
    _ ≤ 5 * U52 := Nat.mul_le_mul_right U52 (by omega)

theorem low_accumulator_prefix_u64 (x y : FiveLimbs) {degree count : ℕ}
    (hdegree : degree < 9) (hcountPos : 0 < count)
    (hcount : count ≤ (lowTerms x y degree).length) :
    (lowTerms x y degree |>.take count).sum < 2 ^ 64 := by
  have hfive : (lowTerms x y degree).length ≤ 5 := by
    rw [low_terms_length x y hdegree]
    exact degree_count_le_five degree
  have hprefix := prefix_sum_lt_five_u52 hcountPos hcount hfive
    (fun term hterm => low_term_lt_u52 x y hdegree hterm)
  calc
    (lowTerms x y degree |>.take count).sum < 5 * U52 := hprefix
    _ < 2 ^ 64 := by norm_num [U52]

theorem high_accumulator_prefix_u64 (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) {degree count : ℕ}
    (hdegree : degree < 9) (hcountPos : 0 < count)
    (hcount : count ≤ (highTerms x y degree).length) :
    (highTerms x y degree |>.take count).sum < 2 ^ 64 := by
  have hfive : (highTerms x y degree).length ≤ 5 := by
    rw [high_terms_length x y hdegree]
    exact degree_count_le_five degree
  have hprefix := prefix_sum_lt_five_u52 hcountPos hcount hfive
    (fun term hterm => high_term_lt_u52 x y hx hy hdegree hterm)
  calc
    (highTerms x y degree |>.take count).sum < 5 * U52 := hprefix
    _ < 2 ^ 64 := by norm_num [U52]

theorem low_terms_sum_bound (x y : FiveLimbs) {degree : ℕ} (hdegree : degree < 9) :
    (lowTerms x y degree).sum < degreeCount degree * U52 := by
  have hne : lowTerms x y degree ≠ [] := by
    intro hempty
    have hzero := congrArg List.length hempty
    rw [low_terms_length x y hdegree] at hzero
    simp at hzero
    exact (Nat.ne_of_gt (degree_count_pos hdegree)) hzero
  simpa [low_terms_length x y hdegree] using
    list_sum_lt_length_mul_u52 hne
      (fun term hterm => low_term_lt_u52 x y hdegree hterm)

theorem high_terms_sum_bound (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) {degree : ℕ} (hdegree : degree < 9) :
    (highTerms x y degree).sum < degreeCount degree * U52 := by
  have hne : highTerms x y degree ≠ [] := by
    intro hempty
    have hzero := congrArg List.length hempty
    rw [high_terms_length x y hdegree] at hzero
    simp at hzero
    exact (Nat.ne_of_gt (degree_count_pos hdegree)) hzero
  simpa [high_terms_length x y hdegree] using
    list_sum_lt_length_mul_u52 hne
      (fun term hterm => high_term_lt_u52 x y hx hy hdegree hterm)

theorem high_accumulator_shift_u64 (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) {degree : ℕ} (hdegree : degree < 9) :
    2 * (highTerms x y degree).sum < 2 ^ 64 := by
  have hsum := high_terms_sum_bound x y hx hy hdegree
  have hcount := degree_count_le_five degree
  calc
    2 * (highTerms x y degree).sum < 2 * (degreeCount degree * U52) :=
      Nat.mul_lt_mul_of_pos_left hsum (by norm_num)
    _ ≤ 2 * (5 * U52) := Nat.mul_le_mul_left 2
      (Nat.mul_le_mul_right U52 hcount)
    _ < 2 ^ 64 := by norm_num [U52]

def groupedDegree (x y : FiveLimbs) : ℕ → ℕ
  | 0 => (lowTerms x y 0).sum
  | 1 => (lowTerms x y 1).sum + 2 * (highTerms x y 0).sum
  | 2 => (lowTerms x y 2).sum + 2 * (highTerms x y 1).sum
  | 3 => (lowTerms x y 3).sum + 2 * (highTerms x y 2).sum
  | 4 => (lowTerms x y 4).sum + 2 * (highTerms x y 3).sum
  | 5 => (lowTerms x y 5).sum + 2 * (highTerms x y 4).sum
  | 6 => (lowTerms x y 6).sum + 2 * (highTerms x y 5).sum
  | 7 => (lowTerms x y 7).sum + 2 * (highTerms x y 6).sum
  | 8 => (lowTerms x y 8).sum + 2 * (highTerms x y 7).sum
  | 9 => 2 * (highTerms x y 8).sum
  | _ => 0

def groupedConvolution (x y : FiveLimbs) : ℕ :=
  ∑ degree ∈ Finset.range 10, groupedDegree x y degree * B ^ degree

def groupedMultiplier : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 10
  | 4 => 13
  | 5 => 14
  | 6 => 11
  | 7 => 8
  | 8 => 5
  | 9 => 2
  | _ => 0

/-!
The ten constants are the exact `COMBINE_HIGH` source-count bounds.  For
example degree 5 contains four low halves and twice five high halves, hence
`4 + 2·5 = 14` units of `2^52`.
-/
theorem grouped_degree_bound (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) {degree : ℕ} (hdegree : degree < 10) :
    groupedDegree x y degree < groupedMultiplier degree * U52 := by
  have l0 := low_terms_sum_bound x y (degree := 0) (by norm_num)
  have l1 := low_terms_sum_bound x y (degree := 1) (by norm_num)
  have l2 := low_terms_sum_bound x y (degree := 2) (by norm_num)
  have l3 := low_terms_sum_bound x y (degree := 3) (by norm_num)
  have l4 := low_terms_sum_bound x y (degree := 4) (by norm_num)
  have l5 := low_terms_sum_bound x y (degree := 5) (by norm_num)
  have l6 := low_terms_sum_bound x y (degree := 6) (by norm_num)
  have l7 := low_terms_sum_bound x y (degree := 7) (by norm_num)
  have l8 := low_terms_sum_bound x y (degree := 8) (by norm_num)
  have h0 := high_terms_sum_bound x y hx hy (degree := 0) (by norm_num)
  have h1 := high_terms_sum_bound x y hx hy (degree := 1) (by norm_num)
  have h2 := high_terms_sum_bound x y hx hy (degree := 2) (by norm_num)
  have h3 := high_terms_sum_bound x y hx hy (degree := 3) (by norm_num)
  have h4 := high_terms_sum_bound x y hx hy (degree := 4) (by norm_num)
  have h5 := high_terms_sum_bound x y hx hy (degree := 5) (by norm_num)
  have h6 := high_terms_sum_bound x y hx hy (degree := 6) (by norm_num)
  have h7 := high_terms_sum_bound x y hx hy (degree := 7) (by norm_num)
  have h8 := high_terms_sum_bound x y hx hy (degree := 8) (by norm_num)
  interval_cases degree <;>
    simp [groupedDegree, groupedMultiplier, degreeCount] at * <;> omega

theorem grouped_degree_u64 (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) {degree : ℕ} (hdegree : degree < 10) :
    groupedDegree x y degree < 2 ^ 64 := by
  have hbound := grouped_degree_bound x y hx hy hdegree
  have hmultiplier : groupedMultiplier degree ≤ 14 := by
    interval_cases degree <;> norm_num [groupedMultiplier]
  calc
    groupedDegree x y degree < groupedMultiplier degree * U52 := hbound
    _ ≤ 14 * U52 := Nat.mul_le_mul_right U52 hmultiplier
    _ < 2 ^ 64 := by norm_num [U52]

theorem grouped_convolution_exact (x y : FiveLimbs) :
    groupedConvolution x y = splitConvolution x y := by
  simp [groupedConvolution, groupedDegree, lowTerms, highTerms,
    splitConvolution, Fin.sum_univ_succ, Finset.sum_range_succ]
  ring

def lowPolynomial (x y : FiveLimbs) : ℕ :=
  groupedDegree x y 0 + groupedDegree x y 1 * B +
    groupedDegree x y 2 * B ^ 2 + groupedDegree x y 3 * B ^ 3 +
    groupedDegree x y 4 * B ^ 4

def highPolynomial (x y : FiveLimbs) : ℕ :=
  groupedDegree x y 5 + groupedDegree x y 6 * B +
    groupedDegree x y 7 * B ^ 2 + groupedDegree x y 8 * B ^ 3 +
    groupedDegree x y 9 * B ^ 4

def foldedGrouped (x y : FiveLimbs) : Loose5 :=
  foldDegrees
    (groupedDegree x y 0) (groupedDegree x y 1) (groupedDegree x y 2)
    (groupedDegree x y 3) (groupedDegree x y 4) (groupedDegree x y 5)
    (groupedDegree x y 6) (groupedDegree x y 7) (groupedDegree x y 8)
    (groupedDegree x y 9)

theorem grouped_polynomial_decomposition (x y : FiveLimbs) :
    groupedConvolution x y =
      lowPolynomial x y + B ^ 5 * highPolynomial x y := by
  simp [groupedConvolution, lowPolynomial, highPolynomial, Finset.sum_range_succ]
  ring

theorem folded_polynomial_decomposition (x y : FiveLimbs) :
    looseValue (foldedGrouped x y) =
      lowPolynomial x y + 19 * highPolynomial x y := by
  simp [foldedGrouped, foldDegrees, looseValue, lowPolynomial, highPolynomial]
  ring

theorem folded_grouped_preserves_mod (x y : FiveLimbs) :
    looseValue (foldedGrouped x y) % P = groupedConvolution x y % P := by
  rw [folded_polynomial_decomposition, grouped_polynomial_decomposition]
  have hfold : (highPolynomial x y * B ^ 5) % P =
      (19 * highPolynomial x y) % P := by
    simpa using fold_monomial_mod (highPolynomial x y) 0
  calc
    (lowPolynomial x y + 19 * highPolynomial x y) % P =
        (lowPolynomial x y % P + (19 * highPolynomial x y) % P) % P :=
          Nat.add_mod _ _ _
    _ = (lowPolynomial x y % P + (highPolynomial x y * B ^ 5) % P) % P := by
      rw [hfold]
    _ = (lowPolynomial x y + highPolynomial x y * B ^ 5) % P :=
      (Nat.add_mod _ _ _).symm
    _ = (lowPolynomial x y + B ^ 5 * highPolynomial x y) % P := by
      congr 2
      ring

/-!
The next two theorems certify the two instructions in each degree-5 fold:
the `VPMULLQ $19` result fits in u64, and the subsequent `VPADDQ` result is
strictly below 2^61.  Thus neither machine instruction wraps.
-/
theorem fold_products_u64 (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) :
    19 * groupedDegree x y 5 < 2 ^ 64 ∧
      19 * groupedDegree x y 6 < 2 ^ 64 ∧
      19 * groupedDegree x y 7 < 2 ^ 64 ∧
      19 * groupedDegree x y 8 < 2 ^ 64 ∧
      19 * groupedDegree x y 9 < 2 ^ 64 := by
  have h5 := grouped_degree_bound x y hx hy (degree := 5) (by norm_num)
  have h6 := grouped_degree_bound x y hx hy (degree := 6) (by norm_num)
  have h7 := grouped_degree_bound x y hx hy (degree := 7) (by norm_num)
  have h8 := grouped_degree_bound x y hx hy (degree := 8) (by norm_num)
  have h9 := grouped_degree_bound x y hx hy (degree := 9) (by norm_num)
  norm_num [groupedMultiplier, U52] at h5 h6 h7 h8 h9 ⊢
  omega

theorem final_carry_ifma_low_exact {foldedLimb4 : ℕ}
    (hfolded : foldedLimb4 < 2 ^ 61) :
    lo52 19 (carry foldedLimb4) = 19 * carry foldedLimb4 := by
  have hcarry := carry_lt_1024_of_u61 hfolded
  have hproduct : 19 * carry foldedLimb4 < U52 := by
    norm_num [U52] at hcarry ⊢
    omega
  simp [lo52, Nat.mod_eq_of_lt hproduct]

theorem folded_grouped_u61 (x y : FiveLimbs)
    (hx : LimbsU52 x) (hy : LimbsU52 y) :
    (foldedGrouped x y).l0 < 2 ^ 61 ∧
      (foldedGrouped x y).l1 < 2 ^ 61 ∧
      (foldedGrouped x y).l2 < 2 ^ 61 ∧
      (foldedGrouped x y).l3 < 2 ^ 61 ∧
      (foldedGrouped x y).l4 < 2 ^ 61 := by
  apply folded_degrees_u61
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 0) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 1) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 2) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 3) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 4) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 5) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 6) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 7) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 8) (by norm_num)
  · simpa [groupedMultiplier] using
      grouped_degree_bound x y hx hy (degree := 9) (by norm_num)

/-!
End-to-end refinement theorem for one lane of `narya_r51x8_mul_ifma`.

The only hypotheses are the native routine's real source contract: each of the
five input limbs is below 2^52.  The earlier abstract `hfold` premise is fully
discharged by the exact row-major trace and the degree-5 fold proof above.
Together with `low_accumulator_prefix_u64` and
`high_accumulator_prefix_u64`, this establishes:

* every VPMADD52 accumulator update is free of u64 wrap;
* every `COMBINE_HIGH` result is free of u64 wrap;
* every `×19` fold multiply and add is free of u64 wrap;
* the carry outputs are valid future IFMA sources; and
* the returned five-limb value is congruent to the input product modulo p.
-/
theorem radix51_mul_assembly_trace_correct
    (x y : FiveLimbs) (hx : LimbsU52 x) (hy : LimbsU52 y) :
    looseValue (normalized (foldedGrouped x y)) % P =
        (radixValue x * radixValue y) % P ∧
      (normalized (foldedGrouped x y)).l0 < U52 ∧
      (normalized (foldedGrouped x y)).l1 < U52 ∧
      (normalized (foldedGrouped x y)).l2 < U52 ∧
      (normalized (foldedGrouped x y)).l3 < U52 ∧
      (normalized (foldedGrouped x y)).l4 < U52 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := folded_grouped_u61 x y hx hy
  apply radix51_mul_correct_of_folded_schedule x y (foldedGrouped x y)
  · calc
      looseValue (foldedGrouped x y) % P = groupedConvolution x y % P :=
        folded_grouped_preserves_mod x y
      _ = splitConvolution x y % P := by
        rw [grouped_convolution_exact]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end NaryaFormal.Radix51.AssemblyTrace
