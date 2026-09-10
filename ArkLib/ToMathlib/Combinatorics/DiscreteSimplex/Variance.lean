/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Combinatorics.DiscreteSimplex.Moments
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Weighted moments and variance of a finite simplex

All averages use the uniform distribution on the canonical `OrdinarySimplex r S`. Weights are
arbitrary real numbers. The exact variance retains `S * (S + d)`, where `d = r + 1`; replacing
this factor by `S²` would discard the finite-size correction. No continuous-volume or optimized
parameter claim is made here.
-/

@[expose] public section

namespace DiscreteSimplex

noncomputable section

open scoped BigOperators

/-- The finite simplex is nonempty even at zero budget or with no coordinates. -/
theorem card_ordinarySimplex_pos (r S : ℕ) : 0 < Fintype.card (OrdinarySimplex r S) := by
  let : Nonempty (OrdinarySimplex r S) := ⟨⟨fun _ ↦ 0, by simp⟩⟩
  exact Fintype.card_pos

/-- Uniform real average over the finite simplex. -/
def simplexAverage {r S : ℕ} (f : OrdinarySimplex r S → ℝ) : ℝ :=
  (∑ u, f u) / Fintype.card (OrdinarySimplex r S)

/-- Weighted coordinate statistic on the finite simplex. -/
def simplexWeightedStatistic {r S : ℕ} (w : Fin r → ℝ) (u : OrdinarySimplex r S) : ℝ :=
  ∑ i, w i * (u.1 i : ℝ)

/-- Exact mean of the weighted statistic, with the slack coordinate assigned weight zero. -/
def simplexWeightedMean {r : ℕ} (S : ℕ) (w : Fin r → ℝ) : ℝ :=
  (S : ℝ) / ((r : ℝ) + 1) * ∑ i, w i

private theorem cast_mul_pred (n : ℕ) :
    (n : ℝ) * ((n - 1 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  cases n <;> simp

private theorem first_moment_real {r S : ℕ} (i : Fin r) :
    ((r : ℝ) + 1) * (∑ u : OrdinarySimplex r S, (u.1 i : ℝ)) =
      (S : ℝ) * Fintype.card (OrdinarySimplex r S) := by
  exact_mod_cast simplex_first_moment (S := S) i

private theorem coordinate_product_moment {r S : ℕ} (i j : Fin r) :
    ((r : ℝ) + 1) * ((r : ℝ) + 2) *
        (∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * (u.1 j : ℝ)) =
      ((S : ℝ) * ((S : ℝ) - 1) +
        if i = j then (S : ℝ) * ((S : ℝ) + ((r : ℝ) + 1)) else 0) *
          Fintype.card (OrdinarySimplex r S) := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hFirst := first_moment_real (S := S) i
    have hFactorial : ((r : ℝ) + 1) * ((r : ℝ) + 2) *
        (∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * ((u.1 i : ℝ) - 1)) =
        2 * (S : ℝ) * ((S : ℝ) - 1) * Fintype.card (OrdinarySimplex r S) := by
      have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (simplex_factorial_moment (S := S) i)
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sum] at h
      rw [mul_assoc 2 (S : ℝ), cast_mul_pred] at h
      simpa only [cast_mul_pred, mul_assoc] using h
    have hSquare : (∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * (u.1 i : ℝ)) =
        (∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * ((u.1 i : ℝ) - 1)) +
          ∑ u : OrdinarySimplex r S, (u.1 i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hSquare, mul_add, hFactorial]
    nlinarith [congrArg (fun x : ℝ ↦ ((r : ℝ) + 2) * x) hFirst]
  · simp only [hij, ite_false, add_zero]
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (simplex_mixed_moment (S := S) i j hij)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sum,
      cast_mul_pred] using h

/-- The weighted first moment before division by the simplex cardinality. -/
theorem simplex_weighted_sum {r S : ℕ} (w : Fin r → ℝ) :
    ((r : ℝ) + 1) * (∑ u : OrdinarySimplex r S, simplexWeightedStatistic w u) =
      (S : ℝ) * Fintype.card (OrdinarySimplex r S) * ∑ i, w i := by
  unfold simplexWeightedStatistic
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  calc
    ((r : ℝ) + 1) * (w i * ∑ u : OrdinarySimplex r S, (u.1 i : ℝ)) =
        w i * (((r : ℝ) + 1) * ∑ u : OrdinarySimplex r S, (u.1 i : ℝ)) := by ring
    _ = (S : ℝ) * Fintype.card (OrdinarySimplex r S) * w i := by
      rw [first_moment_real]
      ring

/-- Exact weighted expectation under uniform finite normalization. -/
theorem simplex_average_weighted {r S : ℕ} (w : Fin r → ℝ) :
    simplexAverage (simplexWeightedStatistic (S := S) w) = simplexWeightedMean S w := by
  have hC : (Fintype.card (OrdinarySimplex r S) : ℝ) ≠ 0 := by
    exact_mod_cast (card_ordinarySimplex_pos r S).ne'
  have hd : (r : ℝ) + 1 ≠ 0 := by positivity
  unfold simplexAverage simplexWeightedMean
  field_simp
  nlinarith [simplex_weighted_sum (S := S) w]

private theorem weighted_square_sum {r S : ℕ} (w : Fin r → ℝ) :
    (∑ u : OrdinarySimplex r S, simplexWeightedStatistic w u ^ 2) =
      ∑ i, ∑ j, w i * w j *
        (∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * (u.1 j : ℝ)) := by
  simp only [simplexWeightedStatistic, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

private theorem weighted_matrix_sum {r : ℕ} (w : Fin r → ℝ) (a b c : ℝ) :
    (∑ i, ∑ j, w i * w j * ((a + if i = j then b else 0) * c)) =
      (a * (∑ i, w i) ^ 2 + b * ∑ i, w i ^ 2) * c := by
  have hTerm : ∀ i j, w i * w j * ((a + if i = j then b else 0) * c) =
      a * c * (w i * w j) + if j = i then b * c * w i ^ 2 else 0 := by
    intro i j
    by_cases h : i = j
    · subst j
      simp only [ite_true]
      ring
    · simp only [h, Ne.symm h, ite_false, add_zero]
      ring
  simp_rw [hTerm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  have hDouble : (∑ i, ∑ j, a * c * (w i * w j)) = a * c * (∑ i, w i) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  rw [hDouble]
  ring

/-- Exact weighted second moment before division by the positive simplex cardinality. -/
theorem simplex_weighted_square_sum {r S : ℕ} (w : Fin r → ℝ) :
    ((r : ℝ) + 1) * ((r : ℝ) + 2) *
        (∑ u : OrdinarySimplex r S, simplexWeightedStatistic w u ^ 2) =
      ((S : ℝ) * ((S : ℝ) - 1) * (∑ i, w i) ^ 2 +
        (S : ℝ) * ((S : ℝ) + ((r : ℝ) + 1)) * ∑ i, w i ^ 2) *
          Fintype.card (OrdinarySimplex r S) := by
  rw [weighted_square_sum, Finset.mul_sum]
  have hTerms : ∀ i, ((r : ℝ) + 1) * ((r : ℝ) + 2) *
      (∑ j, w i * w j * (∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * (u.1 j : ℝ))) =
      ∑ j, w i * w j * (((S : ℝ) * ((S : ℝ) - 1) +
        if i = j then (S : ℝ) * ((S : ℝ) + ((r : ℝ) + 1)) else 0) *
          Fintype.card (OrdinarySimplex r S)) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      ((r : ℝ) + 1) * ((r : ℝ) + 2) *
          (w i * w j * ∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * (u.1 j : ℝ)) =
          w i * w j * (((r : ℝ) + 1) * ((r : ℝ) + 2) *
            ∑ u : OrdinarySimplex r S, (u.1 i : ℝ) * (u.1 j : ℝ)) := by ring
      _ = _ := by rw [coordinate_product_moment]
  simp_rw [hTerms]
  exact weighted_matrix_sum w _ _ _

/-- Closed formula for the uniformly normalized weighted second moment. -/
theorem simplex_average_weighted_square {r S : ℕ} (w : Fin r → ℝ) :
    simplexAverage (fun u : OrdinarySimplex r S ↦ simplexWeightedStatistic w u ^ 2) =
      ((S : ℝ) * ((S : ℝ) - 1) * (∑ i, w i) ^ 2 +
        (S : ℝ) * ((S : ℝ) + ((r : ℝ) + 1)) * ∑ i, w i ^ 2) /
          (((r : ℝ) + 1) * ((r : ℝ) + 2)) := by
  have hC : (Fintype.card (OrdinarySimplex r S) : ℝ) ≠ 0 := by
    exact_mod_cast (card_ordinarySimplex_pos r S).ne'
  have hd : (r : ℝ) + 1 ≠ 0 := by positivity
  have hd' : (r : ℝ) + 2 ≠ 0 := by positivity
  unfold simplexAverage
  field_simp
  nlinarith [simplex_weighted_square_sum (S := S) w]

/-- Exact finite variance, with `d = r + 1` including the slack coordinate. -/
def simplexWeightedVariance {r : ℕ} (S : ℕ) (w : Fin r → ℝ) : ℝ :=
  (S : ℝ) * ((S : ℝ) + ((r : ℝ) + 1)) /
    (((r : ℝ) + 1) ^ 2 * ((r : ℝ) + 2)) *
      (((r : ℝ) + 1) * (∑ i, w i ^ 2) - (∑ i, w i) ^ 2)

private theorem simplex_average_sub_sq {r S : ℕ} (f : OrdinarySimplex r S → ℝ) (m : ℝ) :
    simplexAverage (fun u ↦ (f u - m) ^ 2) =
      simplexAverage (fun u ↦ f u ^ 2) - 2 * m * simplexAverage f + m ^ 2 := by
  have hExpand : (∑ u, (f u - m) ^ 2) =
      (∑ u, f u ^ 2) - 2 * m * (∑ u, f u) +
        Fintype.card (OrdinarySimplex r S) * m ^ 2 := by
    calc
      (∑ u, (f u - m) ^ 2) = ∑ u, (f u ^ 2 - 2 * m * f u + m ^ 2) := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
  have hC : (Fintype.card (OrdinarySimplex r S) : ℝ) ≠ 0 := by
    exact_mod_cast (card_ordinarySimplex_pos r S).ne'
  unfold simplexAverage
  rw [hExpand]
  field_simp

/-- Centering the weighted statistic yields the exact finite-simplex variance. This includes
zero budget and the empty coordinate type, without dividing by either `S` or `r`. -/
theorem simplex_average_centered_square {r S : ℕ} (w : Fin r → ℝ) :
    simplexAverage (fun u : OrdinarySimplex r S ↦
      (simplexWeightedStatistic w u - simplexWeightedMean S w) ^ 2) =
        simplexWeightedVariance S w := by
  rw [simplex_average_sub_sq, simplex_average_weighted_square, simplex_average_weighted]
  have hd : (r : ℝ) + 1 ≠ 0 := by positivity
  have hd' : (r : ℝ) + 2 ≠ 0 := by positivity
  unfold simplexWeightedMean simplexWeightedVariance
  field_simp
  ring

/-- The displayed variance is nonnegative because it is an average of squares. -/
theorem simplexWeightedVariance_nonneg {r : ℕ} (S : ℕ) (w : Fin r → ℝ) :
    0 ≤ simplexWeightedVariance S w := by
  rw [← simplex_average_centered_square]
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

/-- A finite one-sided Chebyshev bound in division-free counting form. A tail subset above
`mean + t` consumes at least `t²` per point from the exact total squared deviation. This does not
claim the sharper Cantelli denominator. -/
theorem simplex_upper_tail_count {r S : ℕ} (w : Fin r → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (tail : Finset (OrdinarySimplex r S))
    (hTail : ∀ u ∈ tail, simplexWeightedMean S w + t ≤ simplexWeightedStatistic w u) :
    t ^ 2 * (tail.card : ℝ) ≤
      Fintype.card (OrdinarySimplex r S) * simplexWeightedVariance S w := by
  have hC : (Fintype.card (OrdinarySimplex r S) : ℝ) ≠ 0 := by
    exact_mod_cast (card_ordinarySimplex_pos r S).ne'
  have hTotal := simplex_average_centered_square (S := S) w
  unfold simplexAverage at hTotal
  have hSum := (div_eq_iff hC).mp hTotal
  calc
    t ^ 2 * (tail.card : ℝ) = ∑ _u ∈ tail, t ^ 2 := by simp [mul_comm]
    _ ≤ ∑ u ∈ tail, (simplexWeightedStatistic w u - simplexWeightedMean S w) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      have h := hTail u hu
      nlinarith [sq_nonneg (simplexWeightedStatistic w u - simplexWeightedMean S w - t)]
    _ ≤ ∑ u : OrdinarySimplex r S,
        (simplexWeightedStatistic w u - simplexWeightedMean S w) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
    _ = Fintype.card (OrdinarySimplex r S) * simplexWeightedVariance S w := by
      simpa [mul_comm] using hSum

/-- This finite two-coordinate example has variance `5/12`, rather than the continuous value
`1/6`; it detects loss of the finite correction while retaining a nontrivial mixed term. -/
example : simplexAverage (fun u : OrdinarySimplex 2 2 ↦
    (simplexWeightedStatistic ![1, 1 / 2] u - 1) ^ 2) = 5 / 12 := by
  have h := simplex_average_centered_square (S := 2) ![1, 1 / 2]
  norm_num [simplexWeightedMean, simplexWeightedVariance, Fin.sum_univ_succ] at h
  exact h

end
end DiscreteSimplex
