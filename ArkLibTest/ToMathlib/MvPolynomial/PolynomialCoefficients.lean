/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Extension
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

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2

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

/-- Flattening a constant coefficient of degree one bounds the distinguished-variable degree. -/
example :
    ((optionEquivRight ℚ Unit).symm (C (Polynomial.X : Polynomial ℚ)) :
      MvPolynomial (Option Unit) ℚ).weightedTotalDegree
        (fun i ↦ i.elim 1 (fun _ ↦ 0)) ≤ 1 := by
  exact weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le
    ((coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)) :
      CoeffNatDegreeLE (C Polynomial.X : MvPolynomial Unit (Polynomial ℚ)) 1)

/-- Clearing a degree-one substitution into a degree-one coefficient gives degree at most `2`. -/
example : CoeffNatDegreeLE
    (clearedSubstitution C (C (Polynomial.X : Polynomial ℚ) :
        MvPolynomial Unit (Polynomial ℚ))
      (fun _ : Unit ↦ C (Polynomial.X : Polynomial ℚ)) (fun _ ↦ 1) 1
      (X () : MvPolynomial Unit (Polynomial ℚ))) 2 := by
  exact CoeffNatDegreeLE.clearedSubstitution
    (S := C (Polynomial.X : Polynomial ℚ))
    (N := fun _ : Unit ↦ C (Polynomial.X : Polynomial ℚ))
    (d := fun _ : Unit ↦ 1) (H := 1) (h := 1) (Q := X ())
    (coeffNatDegreeLE_C (by simp))
    (fun _ ↦ coeffNatDegreeLE_C (by simp))
    (by
      intro m hm
      have hm' : m = Finsupp.single () 1 := by
        rw [support_X] at hm
        exact Finset.mem_singleton.mp hm
      subst m
      simp [Finsupp.weight_apply])
    (fun m _ ↦ ((coeffNatDegreeLE_X ()).mono (by norm_num)) m)

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

/-- Evaluation into `E₄` after mapping coefficients sends `tY` to `zY` in either order. -/
example (z : E₄) :
    let f : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
    let Q : MvPolynomial Unit (Polynomial (ZMod 2)) :=
      MvPolynomial.C Polynomial.X * MvPolynomial.X ()
    MvPolynomial.map (Polynomial.evalRingHom z) (MvPolynomial.map (Polynomial.mapRingHom f) Q) =
        (MvPolynomial.C z : MvPolynomial Unit E₄) * MvPolynomial.X () ∧
      MvPolynomial.map (Polynomial.eval₂RingHom f z) Q =
        (MvPolynomial.C z : MvPolynomial Unit E₄) * MvPolynomial.X () := by
  intro f Q
  constructor
  · rw [MvPolynomial.eval_map_coefficients]
    simp [Q]
  · simp [Q]

end

end MvPolynomial
