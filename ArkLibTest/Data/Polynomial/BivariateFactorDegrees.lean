/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.BivariateFactorDegrees

/-!
# Bivariate factor-degree acceptance tests

Check the normalized-factor interface over a coefficient ring that is not a field, the donor's
positive-outer-degree selection, indexed products with repeated factors, and unequal axis degrees.
-/

open Polynomial Polynomial.Bivariate

example (p : ℤ[X][Y]) (hp : p ≠ 0) :
    let s := (UniqueFactorizationMonoid.normalizedFactors p).toFinset.filter
      (fun q ↦ 0 < q.natDegree)
    (∑ q ∈ s, q.natDegree) ≤ p.natDegree ∧ (∑ q ∈ s, degreeX q) ≤ degreeX p := by
  exact sum_natDegree_degreeX_le_of_subset_normalizedFactors hp _ (Finset.filter_subset _ _)

example (p q : ℚ[X][Y]) (hq : q ≠ 0) (h : p ^ 2 ∣ q) :
    2 * p.natDegree ≤ q.natDegree ∧ 2 * degreeX p ≤ degreeX q := by
  have hprod : (∏ _i ∈ (Finset.univ : Finset (Fin 2)), p) ∣ q := by
    simpa using h
  simpa using sum_natDegree_degreeX_le_of_prod_dvd Finset.univ (fun _i : Fin 2 ↦ p) hq hprod

example : (Polynomial.monomial 3 ((X : ℚ[X]) ^ 5)).natDegree = 3 ∧
    degreeX (Polynomial.monomial 3 ((X : ℚ[X]) ^ 5)) = 5 := by
  simp [degreeX]
