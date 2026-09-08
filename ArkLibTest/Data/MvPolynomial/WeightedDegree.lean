/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Weighted-degree acceptance tests

Check mixed zero and positive weights with unequal exponents, repeated indexed factors, an
infinite variable type, and the empty product without assuming the coefficient ring nontrivial.
-/

open MvPolynomial

example : weightedTotalDegree (![0, 2] : Fin 2 → ℕ)
    ((X 0 : MvPolynomial (Fin 2) ℤ) ^ 5 * X 1 ^ 3) = 6 := by
  rw [weightedTotalDegree_mul _ _ _ (pow_ne_zero _ (X_ne_zero 0)) (pow_ne_zero _ (X_ne_zero 1))]
  simp [weightedTotalDegree, support_X_pow, Finsupp.weight_single]

example (w : ℕ → ℕ) (p q : MvPolynomial ℕ ℤ) (hq : q ≠ 0) (h : p ^ 2 ∣ q) :
    2 * weightedTotalDegree w p ≤ weightedTotalDegree w q := by
  have hprod : (∏ _i ∈ (Finset.univ : Finset (Fin 2)), p) ∣ q := by
    simpa using h
  simpa using sum_weightedTotalDegree_le_of_prod_dvd w Finset.univ
    (fun _i : Fin 2 ↦ p) hq hprod

example {σ R : Type*} [CommSemiring R] [NoZeroDivisors R] (w : σ → ℕ) :
    weightedTotalDegree w (1 : MvPolynomial σ R) = 0 := by
  simpa using weightedTotalDegree_prod w (∅ : Finset Unit) (fun _ ↦ (1 : MvPolynomial σ R))
    (by simp)
