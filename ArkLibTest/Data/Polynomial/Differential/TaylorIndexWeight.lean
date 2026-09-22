/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorIndexWeight
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for the coefficient-index weight of a universal Taylor residual

The examples evaluate `indexWeight`, compute the first-order weighted degree of `Y₁` and of
`Y₀ ^ 5`, and show that the index-weight bound is attained by the monomial `c₂` in the coefficient
of `ξ` in the residual of `Y₁` on a chart of length `3`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- `indexWeight` gives `none` weight zero and `some l` weight `l`. -/
example : indexWeight 3 none = 0 ∧ indexWeight 3 (some 2) = 2 := ⟨rfl, rfl⟩

/-- `indexWeight n` is `fun i ↦ i.elim 0 Fin.val`. -/
example (n : ℕ) : indexWeight n = fun i ↦ i.elim 0 Fin.val := rfl

/-- The first-order equation `Q = Y₁`. -/
private abbrev firstJet : DifferentialPolynomial ℚ 1 := X (some 1)

/-- The weighted degree of `Y₁` in which `Y_j` has weight `j` is `1`. -/
private theorem weightedTotalDegree_firstJet :
    firstJet.weightedTotalDegree (indexWeight 2) = 1 := by
  rw [weightedTotalDegree_indexWeight_eq_jetDegree_one, jetDegree, degreeOf_X_self]

/-- The weighted degree of `Y₀ ^ 5` in which `Y_j` has weight `j` is `0`, although its total
degree is `5`. -/
example :
    (X (some 0) ^ 5 : DifferentialPolynomial ℚ 1).weightedTotalDegree (indexWeight 2) = 0 ∧
      (X (some 0) ^ 5 : DifferentialPolynomial ℚ 1).totalDegree = 5 := by
  constructor
  · rw [weightedTotalDegree_indexWeight_eq_jetDegree_one, jetDegree,
      degreeOf_X_pow_of_ne _ (by decide)]
  · rw [totalDegree_X_pow]

/-- On a chart of length `3`, the coefficient of `ξ` in the residual of `Y₁` is `2 c₂`. -/
private theorem firstJet_residual_coeff_one :
    (optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff 1 =
      C 2 * X 2 := by
  have hres : universalTaylorResidual 3 (0 : ℚ) firstJet = universalTaylorJet 3 1 := by
    simp [universalTaylorResidual, firstJet]
  rw [hres, optionEquivLeft_universalTaylorJet, Polynomial.hasseDeriv_coeff]
  simp [Fin.sum_univ_three, Polynomial.coeff_monomial]
  rfl

/-- The index-weight bound is attained: `c₂` occurs in the coefficient of `ξ` in the residual of
`Y₁`, and its index weight `2` equals `1 + 1`. -/
example :
    Finsupp.single (2 : Fin 3) 1 ∈
        ((optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff 1).support ∧
      Finsupp.weight Fin.val (Finsupp.single (2 : Fin 3) 1) =
        1 + firstJet.weightedTotalDegree (indexWeight 2) := by
  refine ⟨?_, by simp [Finsupp.weight_single, weightedTotalDegree_firstJet]⟩
  rw [firstJet_residual_coeff_one, mem_support_iff, X, C_mul_monomial, coeff_monomial]
  norm_num

/-- The bound for the residual of `Y₁` on a chart of length `3`: every monomial of the
coefficient of `ξ ^ h` has index weight at most `h + 1`. -/
example (h : ℕ) (m : Fin 3 →₀ ℕ)
    (hm : m ∈
      ((optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff h).support) :
    Finsupp.weight Fin.val m ≤ h + 1 := by
  simpa [weightedTotalDegree_firstJet] using
    indexWeight_le_of_mem_universalTaylorResidual_coeff 3 0 firstJet h m hm

end

end PolynomialDifferential
