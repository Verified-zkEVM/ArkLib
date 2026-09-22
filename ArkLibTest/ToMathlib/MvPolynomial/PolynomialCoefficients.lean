/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.ComputeDegree

/-!
# Acceptance tests for multivariate polynomials with polynomial coefficients

The main example is `P = C t * Y`, a polynomial in one variable `Y` whose coefficient is the
variable `t` of `ℚ[t]`. Its coefficients have degree at most `1` in `t`, its total degree in `Y`
is `1`, and its joint total degree is `2`, so the bound
`jointTotalDegree_le_of_natDegree_coeff_le` is attained. A coefficient affine in `t` has joint
total degree at most `1`.

Over the zero ring every polynomial is zero, so a variable has joint total degree `0`; the
hypothesis `Nontrivial R` of `jointTotalDegree_X` is needed.
-/

namespace MvPolynomial

noncomputable section

/-- The polynomial `t * Y` with the parameter `t` in the coefficient ring `ℚ[t]`. -/
private abbrev paramTimesVar : MvPolynomial Unit (Polynomial ℚ) :=
  C Polynomial.X * X ()

/-- The coefficients of `t * Y` have degree at most `1` in `t`. -/
example : CoeffNatDegreeLE paramTimesVar 1 := by
  simpa using (coeffNatDegreeLE_C (σ := Unit) (p := (Polynomial.X : Polynomial ℚ))
    (by simp)).mul (coeffNatDegreeLE_X ())

/-- Differentiating `t * Y` in `Y` keeps the coefficient degree bound `1`. -/
example : CoeffNatDegreeLE (pderiv () paramTimesVar) 1 := by
  apply CoeffNatDegreeLE.pderiv
  simpa using (coeffNatDegreeLE_C (σ := Unit) (p := (Polynomial.X : Polynomial ℚ))
    (by simp)).mul (coeffNatDegreeLE_X ())

/-- `t * Y` has joint total degree `2`: it becomes `X none * X (some ())`. -/
private theorem jointTotalDegree_paramTimesVar : jointTotalDegree paramTimesVar = 2 := by
  have h : (optionEquivRight ℚ Unit).symm paramTimesVar =
      monomial (Finsupp.single none 1 + Finsupp.single (some ()) 1) 1 := by
    rw [paramTimesVar, map_mul, optionEquivRight_symm_C, optionEquivRight_symm_X,
      Polynomial.aeval_X, X, X, monomial_mul_monomial, one_mul]
  rw [jointTotalDegree, h, totalDegree_monomial _ one_ne_zero,
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  simp

/-- The bound `jointTotalDegree P ≤ h + totalDegree P` is attained by `t * Y` with `h = 1`. -/
example : jointTotalDegree paramTimesVar = 1 + paramTimesVar.totalDegree := by
  rw [jointTotalDegree_paramTimesVar]
  have : paramTimesVar.totalDegree = 1 := by
    rw [paramTimesVar, C_mul_X_eq_monomial, totalDegree_monomial _ Polynomial.X_ne_zero]
    simp
  omega

/-- The bound of `jointTotalDegree_le_of_natDegree_coeff_le` applied to `t * Y`. -/
example : jointTotalDegree paramTimesVar ≤ 1 + 1 := by
  refine (jointTotalDegree_le_of_natDegree_coeff_le _ 1 fun m _ ↦ ?_).trans ?_
  · exact ((coeffNatDegreeLE_C (σ := Unit) (p := (Polynomial.X : Polynomial ℚ))
      (by simp)).mul (coeffNatDegreeLE_X ())) m
  · exact Nat.add_le_add_left ((totalDegree_mul _ _).trans (by simp)) 1

/-- A coefficient affine in the parameter has joint total degree at most `1`. -/
example (a b : ℚ) :
    jointTotalDegree (C (Polynomial.C a + Polynomial.X * Polynomial.C b) :
      MvPolynomial Unit (Polynomial ℚ)) ≤ 1 :=
  (jointTotalDegree_C_le _).trans (by compute_degree)

/-- Over the zero ring the variable is zero, so it has joint total degree `0`, not `1`. -/
example : jointTotalDegree (X () : MvPolynomial Unit (Polynomial (ZMod 1))) = 0 := by
  rw [Subsingleton.elim (X () : MvPolynomial Unit (Polynomial (ZMod 1))) 0]
  simp [jointTotalDegree]

/-- `optionEquivLeft` commutes with reducing the coefficients modulo `2`. -/
example (Q : MvPolynomial (Option Unit) ℤ) :
    Polynomial.map (map (Int.castRingHom (ZMod 2))) (optionEquivLeft ℤ Unit Q) =
      optionEquivLeft (ZMod 2) Unit (map (Int.castRingHom (ZMod 2)) Q) :=
  map_optionEquivLeft _ Q

end

end MvPolynomial
