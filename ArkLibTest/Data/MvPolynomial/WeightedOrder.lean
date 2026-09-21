/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightedOrder

/-!
# Weighted-order acceptance tests

These examples check lower weighted-order bounds with nonuniform weights, the boundary where the
bound equals the weight, a concrete weighted truncation, and the truncation-before-substitution
identity for a substitution that sends a variable of weight one to a product of weight two.
-/

open MvPolynomial

/-- With weights `(1, 2)`, `X₀ X₁` has order exactly `3`: it meets the bound `3` and fails `4`. -/
example :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ∈ restrictWeightedOrder ![1, 2] 3 ∧
      (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ∉ restrictWeightedOrder ![1, 2] 4 := by
  constructor
  · simpa using mul_mem_restrictWeightedOrder
      (X_mem_restrictWeightedOrder (R := ℤ) ![1, 2] 0 le_rfl)
      (X_mem_restrictWeightedOrder (R := ℤ) ![1, 2] 1 le_rfl)
  · rw [X, X, monomial_mul_monomial, monomial_mem_restrictWeightedOrder]
    norm_num [Finsupp.weight_single]

/-- Truncating `1 + X₀ + X₁` below weight `2` removes exactly `X₁`. -/
example :
    weightedTruncation ![1, 2] 2 (1 + X 0 + X 1 : MvPolynomial (Fin 2) ℚ) = 1 + X 0 := by
  have a : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    simp [Finsupp.single_eq_single_iff]
  have b : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 :=
    (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  ext e
  by_cases h0 : e = 0
  · subst h0
    simp [coeff_X]
  by_cases h1 : e = Finsupp.single 0 1
  · subst h1
    simp [coeff_X, coeff_one, Finsupp.weight_single, a]
  by_cases h2 : e = Finsupp.single 1 1
  · subst h2
    simp [coeff_X, coeff_one, Finsupp.weight_single, b, a.symm]
  simp [coeff_X, coeff_one, Ne.symm h0, Ne.symm h1, Ne.symm h2]

/-- Every polynomial has weighted order at least zero. -/
example (p : MvPolynomial (Fin 2) ℤ) : p ∈ restrictWeightedOrder ![1, 2] 0 := by
  simp

/-- Substituting `X ↦ Y²` doubles the weight, so truncating the source below weight `3` does not
change the target truncated below weight `3`. -/
example (F : MvPolynomial Unit ℚ) :
    weightedTruncation (fun _ : Unit => 1) 3
        (bind₁ (fun _ => X () ^ 2) (weightedTruncation (fun _ : Unit => 2) 3 F)) =
      weightedTruncation (fun _ : Unit => 1) 3 (bind₁ (fun _ => X () ^ 2) F) := by
  refine weightedTruncation_bind₁_weightedTruncation (fun _ => ?_) 3 F
  simpa using pow_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := ℚ) (fun _ : Unit => 1) () le_rfl) 2

/-- A `filterSupport` and its complement add back to the original polynomial. -/
example (F : MvPolynomial (Fin 2) ℚ) :
    filterSupport (fun e => e 0 = 0) F + filterSupport (fun e => ¬e 0 = 0) F = F :=
  filterSupport_add_filterSupport_not _ F
