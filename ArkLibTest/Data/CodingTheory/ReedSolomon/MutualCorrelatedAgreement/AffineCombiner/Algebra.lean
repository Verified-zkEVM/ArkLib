/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.TaylorChart
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.PersistenceDescent
import Mathlib.Basic.Complex.Basic

/-! # Acceptance cases for coefficient descent and regular Taylor reconstruction -/

open ReedSolomon Polynomial

/-- The equation `Z² - X²`, singular at the origin. -/
private noncomputable def singularR : MvPolynomial AffineVar ℚ :=
  MvPolynomial.X none ^ 2 - MvPolynomial.X (some 0) ^ 2

-- Initial value and challenge do not determine a root at a singular center.
example : affineLineEval 0 0 (X : ℚ[X]) singularR = 0 := by simp [singularR]
example : affineLineEval 0 0 (-X : ℚ[X]) singularR = 0 := by simp [singularR]
example : (X : ℚ[X]).eval 0 = (-X : ℚ[X]).eval 0 := by simp
example : (X : ℚ[X]) ≠ -X := by
  intro h
  have h1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h
  norm_num at h1

-- A witness with genuinely non-base-field coefficients descends to rational coefficients.
example : ∃ H₀ L₀ : ℚ[X], L₀ ≠ 0 ∧ L₀.degree ≤ 1 ∧ H₀.degree ≤ 1 ∧
    ∀ k : Fin 2, H₀.eval (k : ℚ) = L₀.eval (k : ℚ) * (k : ℚ) := by
  apply exists_lineRatioWitness_of_map (algebraMap ℚ ℂ)
    (fun k : Fin 2 ↦ (k : ℚ)) (fun k : Fin 2 ↦ (k : ℚ)) 1
    (H := C Complex.I * X) (L := C Complex.I)
  · exact C_ne_zero.mpr Complex.I_ne_zero
  · simp
  · compute_degree; norm_num
  · intro k
    simp

#print axioms ReedSolomon.totalDegree_affineChartNumerator_le
#print axioms ReedSolomon.exists_lineRatioWitness_of_map
#print axioms Matrix.exists_mulVec_eq_zero_apply_ne_zero_of_map
