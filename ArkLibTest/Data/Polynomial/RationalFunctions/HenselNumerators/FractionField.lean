/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.FractionField

/-! Ordinary-import clients for fraction-field-separable lifts and their separability boundary. -/

open Polynomial Polynomial.Bivariate

namespace AdapterTest
noncomputable section
open RationalFunctions RationalFunctions.HenselNumerators
local notation "K" => FractionRing ℚ[X]
private def R : ℚ[X][X][Y] := Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X
private def H : ℚ[X][Y] := Polynomial.X
private instance : Fact (Irreducible H) := ⟨by exact Polynomial.irreducible_X⟩
private instance : Fact (0 < H.natDegree) := ⟨by simp [H]⟩

example : ∃ αseq : ℕ → 𝕃 H,
    αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
    evalRAtPowerSeries 0 H R (gammaFromAlpha H αseq) = 0 := by
  apply exists_hensel_alpha_sequence_of_fractionField_separable K 0 R H
  · refine ⟨Polynomial.C Polynomial.X, ?_⟩
    simp [R, H, Bivariate.evalX, Polynomial.C_mul_X_eq_monomial]
  · have hx : algebraMap ℚ[X] K Polynomial.X ≠ 0 := by
      intro h
      apply Polynomial.X_ne_zero (R := ℚ)
      apply IsFractionRing.injective ℚ[X] K
      exact h.trans (map_zero _).symm
    rw [Polynomial.separable_def]
    refine ⟨0, Polynomial.C ((algebraMap ℚ[X] K Polynomial.X)⁻¹), ?_⟩
    simp [R, Bivariate.evalX, ← Polynomial.C_mul, hx]

example : ¬ (Polynomial.C Polynomial.X * Polynomial.X : ℚ[X][Y]).Separable := by
  intro h
  have hm := h.map (f := Polynomial.evalRingHom (0 : ℚ))
  exact Polynomial.not_separable_zero (by simpa using hm)

example : ¬ (Polynomial.X ^ 2 : K[X]).Separable := by
  intro h
  have := (h.of_pow Polynomial.not_isUnit_X (by decide : (2 : ℕ) ≠ 0)).2
  norm_num at this
end
end AdapterTest

#print axioms RationalFunctions.HenselNumerators.initial_root_at_x0_of_dvd
#print axioms RationalFunctions.HenselNumerators.zeta_ne_zero_of_fractionField_separable
#print axioms
  RationalFunctions.HenselNumerators.exists_hensel_alpha_sequence_of_fractionField_separable
