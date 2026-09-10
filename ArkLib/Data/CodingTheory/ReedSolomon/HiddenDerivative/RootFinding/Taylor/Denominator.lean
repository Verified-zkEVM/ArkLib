/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Support

/-!
# Common denominator budget for rational Taylor lifting

The Taylor-order support bound implies that a residual of order `h`, before adding
coefficient `c_(r+h)`, uses at most `2h-2` powers of the separant denominator.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

/-- Later-coefficient denominator exponents fit in `2h-2` before the order-`h` lift. -/
theorem taylor_denominator_weight_le {r h : ℕ} (hh : 0 < h)
    (m : Fin (r + h) →₀ ℕ)
    (hm : Finsupp.weight (fun l : Fin (r + h) ↦ l.val - r) m ≤ h) :
    Finsupp.weight (fun l : Fin (r + h) ↦ 2 * (l.val - r) - 1) m ≤ 2 * h - 2 := by
  classical
  let W := Finsupp.weight (fun l : Fin (r + h) ↦ l.val - r) m
  let D := Finsupp.weight (fun l : Fin (r + h) ↦ 2 * (l.val - r) - 1) m
  let C := Finsupp.weight (fun l : Fin (r + h) ↦ if r < l.val then 1 else 0) m
  have heq : D + C = 2 * W := by
    simp only [D, C, W, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : r < l.val
    · simp only [if_pos hl]
      have hpos : 0 < l.val - r := by omega
      have ht : 2 * (l.val - r) - 1 + 1 = 2 * (l.val - r) := by omega
      nlinarith
    · simp [if_neg hl, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hl)]
  have hmax : W ≤ (h - 1) * C := by
    simp only [W, C, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    by_cases hl : r < l.val
    · simp only [if_pos hl, mul_one]
      have hweight : l.val - r ≤ h - 1 := by omega
      nlinarith
    · simp [if_neg hl, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hl)]
  change D ≤ 2 * h - 2
  by_cases hC : 2 ≤ C
  · omega
  · have hc : C = 0 ∨ C = 1 := by omega
    rcases hc with hc | hc <;> rw [hc] at hmax heq <;>
      simp only [mul_zero, mul_one] at hmax <;> omega

/-- The actual truncated universal residual satisfies the separant-denominator budget. -/
theorem denominator_weight_le_of_mem_universalTaylorResidual_coeff
    {F : Type*} [CommSemiring F] {r h : ℕ} (hh : 0 < h) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) (m : Fin (r + h) →₀ ℕ)
    (hm : m ∈ ((MvPolynomial.optionEquivLeft F (Fin (r + h))
      (universalTaylorResidual (r + h) center Q)).coeff h).support) :
    Finsupp.weight (fun l : Fin (r + h) ↦ 2 * (l.val - r) - 1) m ≤ 2 * h - 2 :=
  taylor_denominator_weight_le hh m
    (weight_le_of_mem_universalTaylorResidual_coeff (r + h) center Q h m hm)

end ReedSolomon.HiddenDerivative
