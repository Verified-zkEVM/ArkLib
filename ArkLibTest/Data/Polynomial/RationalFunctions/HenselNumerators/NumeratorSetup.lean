/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Setup

/-! Ordinary-import clients for the weak Hensel numerator setup and its weight endpoint. -/

open Polynomial Polynomial.Bivariate

namespace NumeratorSetupTest
noncomputable section
open RationalFunctions RationalFunctions.HenselNumerators

private def H : ℚ[X][Y] := Polynomial.X

private def R : ℚ[X][X][Y] :=
  Polynomial.X + Polynomial.C Polynomial.X * Polynomial.X ^ 2

private instance : Fact (Irreducible H) := ⟨by exact Polynomial.irreducible_X⟩
private instance : Fact (0 < H.natDegree) := ⟨by simp [H]⟩

private lemma evalX_R : Bivariate.evalX (Polynomial.C (0 : ℚ)) R = H := by
  simp [R, H, Bivariate.evalX_eq_map]

private theorem weakSetup : NumeratorHypotheses 0 R H where
  dvd_evalX := by rw [evalX_R]
  evalX_ne := by rw [evalX_R]; exact Polynomial.X_ne_zero
  fullDegreeCofactorUnit Q hQ _ := by
    rw [evalX_R] at hQ
    have hQ_one : Q = 1 := by
      apply mul_left_cancel₀ (show H ≠ 0 by simp [H])
      exact hQ.symm.trans (mul_one H).symm
    rw [hQ_one]
    simp

/-- A client can construct and bound the actual cleared numerator without `Hypotheses`. -/
example : regularWeight (H := H) (by simp [H])
    (xiOfNumeratorHypotheses 0 R H weakSetup) 2 ≤
      WithBot.some ((Bivariate.natDegreeY R - 1) *
        (2 - Bivariate.natDegreeY H + 1)) := by
  have hRdeg : 2 ≤ Bivariate.natDegreeY R := by
    apply Polynomial.le_natDegree_of_ne_zero
    norm_num [R, Polynomial.coeff_X]
  have hD_H : Bivariate.totalDegree H ≤ 2 := by
    norm_num [H, Bivariate.totalDegree]
  have hD_R : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C 0) R) ≤ 2 := by
    rw [evalX_R]
    exact hD_H
  exact xiOfNumeratorHypotheses_weight_le (R := R) (H := H) 0 (by simp [H]) weakSetup
    hRdeg (D := 2) hD_H hD_R

private def quadratic : ℚ[X][Y] := Polynomial.X ^ 2 - Polynomial.C Polynomial.X

private def quadraticR : ℚ[X][X][Y] :=
  Polynomial.X ^ 2 - Polynomial.C (Polynomial.C Polynomial.X)

private lemma evalX_quadraticR :
    Bivariate.evalX (Polynomial.C (0 : ℚ)) quadraticR = quadratic := by
  simp [quadraticR, quadratic, Bivariate.evalX_eq_map]

/-- The motivating `Y² - Z` example satisfies the weak setup directly. -/
example : NumeratorHypotheses 0 quadraticR quadratic where
  dvd_evalX := by rw [evalX_quadraticR]
  evalX_ne := by
    rw [evalX_quadraticR]
    exact Polynomial.X_pow_sub_C_ne_zero (by decide) Polynomial.X
  fullDegreeCofactorUnit Q hQ _ := by
    rw [evalX_quadraticR] at hQ
    have hquadratic_ne : quadratic ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by decide) Polynomial.X
    have hQ_one : Q = 1 := by
      apply mul_left_cancel₀ hquadratic_ne
      exact hQ.symm.trans (mul_one quadratic).symm
    rw [hQ_one]
    simp

/-- Yet `Y² - Z` is not separable over `ℚ[Z]`, so the old setup cannot be constructed from
coefficient-ring separability. -/
example : ¬ quadratic.Separable := by
  intro h
  have hm := h.map (f := Polynomial.evalRingHom (0 : ℚ))
  have hpow : (Polynomial.X ^ 2 : ℚ[X]).Separable := by
    simpa [quadratic] using hm
  have hunit := (hpow.of_pow Polynomial.not_isUnit_X (by decide : (2 : ℕ) ≠ 0)).2
  norm_num at hunit

end
end NumeratorSetupTest

#print axioms RationalFunctions.HenselNumerators.Hypotheses.toNumeratorHypotheses
#print axioms RationalFunctions.HenselNumerators.embeddingOf𝒪Into𝕃_xiOfNumeratorHypotheses
#print axioms RationalFunctions.HenselNumerators.xiOfNumeratorHypotheses_weight_le
