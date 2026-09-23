/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Acceptance tests for coefficient-degree bounds and flattening

The examples test coefficient bounds under clearing a substitution, and the flattening of
coefficient and jet degree bounds to a bidegree bound.
-/

open MvPolynomial

namespace PolynomialCoefficientsTest

noncomputable section

/-- The polynomial `t * Y` with parameter `t` in the coefficient ring `ℚ[t]`. -/
private abbrev paramTimesVar : MvPolynomial Unit (Polynomial ℚ) :=
  C Polynomial.X * X ()

/-- Flattening a constant coefficient of degree one bounds the distinguished-variable degree. -/
example :
    ((optionEquivRight ℚ Unit).symm (C (Polynomial.X : Polynomial ℚ)) :
      MvPolynomial (Option Unit) ℚ).weightedTotalDegree
        (fun i ↦ i.elim 1 (fun _ ↦ 0)) ≤ 1 := by
  exact weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le
    ((coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)) :
      CoeffNatDegreeLE (C Polynomial.X : MvPolynomial Unit (Polynomial ℚ)) 1)

private abbrev clearedDegreeTwoExample : MvPolynomial Unit (Polynomial ℚ) :=
  clearedSubstitution C (C (Polynomial.X : Polynomial ℚ))
    (fun _ : Unit ↦ C (Polynomial.X : Polynomial ℚ)) (fun _ ↦ 1) 1
    (C (Polynomial.X : Polynomial ℚ) * X ())

/-- Clearing a substitution attains the degree-two coefficient bound for `t * Y`. -/
example : CoeffNatDegreeLE clearedDegreeTwoExample 2 ∧
    (clearedDegreeTwoExample.coeff 0).natDegree = 2 := by
  constructor
  · apply CoeffNatDegreeLE.clearedSubstitution
      (S := C (Polynomial.X : Polynomial ℚ))
      (N := fun _ : Unit ↦ C (Polynomial.X : Polynomial ℚ))
      (d := fun _ : Unit ↦ 1) (H := 1) (h := 1)
      (Q := C (Polynomial.X : Polynomial ℚ) * X ())
    · exact coeffNatDegreeLE_C (by simp)
    · intro _
      exact coeffNatDegreeLE_C (by simp)
    · intro m hm
      have hm' : m = Finsupp.single () 1 := by
        change m ∈ (C (Polynomial.X : Polynomial ℚ) * X ()).support at hm
        rw [C_mul_X_eq_monomial] at hm
        exact Finset.mem_singleton.mp (support_monomial_subset hm)
      subst m
      simp [Finsupp.weight_apply]
    · intro m _
      have hcoeff : CoeffNatDegreeLE
          (C (Polynomial.X : Polynomial ℚ) * X ()) 1 := by
        exact (coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)).mul
          (coeffNatDegreeLE_X ())
      exact hcoeff m
  · simp [clearedDegreeTwoExample, clearedSubstitution, C_mul_X_eq_monomial,
      support_monomial, Finsupp.weight_apply]

/-- The coefficient and jet degree bounds flatten to bidegree `(1, 1)` for `tY`. -/
example : (optionEquivRight ℚ Unit).symm paramTimesVar ∈
    restrictBidegree Unit ℚ 1 1 := by
  have hheight : CoeffNatDegreeLE paramTimesVar 1 := by
    exact (coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)).mul
      (coeffNatDegreeLE_X ())
  have hjet : paramTimesVar.totalDegree ≤ 1 := by
    rw [paramTimesVar, C_mul_X_eq_monomial,
      totalDegree_monomial _ Polynomial.X_ne_zero]
    simp
  exact optionEquivRight_symm_mem_restrictBidegree hheight hjet

end

end PolynomialCoefficientsTest
