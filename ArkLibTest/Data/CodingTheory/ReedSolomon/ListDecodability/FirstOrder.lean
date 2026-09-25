/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Bounds
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# First-order Reed–Solomon list-bound acceptance cases

Concrete examples exercise the automatic complete-list theorem and the profile-based finite-family
theorem over `ℚ`.
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

private def rationalEvaluationDomain : Fin 4 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), fun i j h ↦ by
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact Fin.ext (by exact_mod_cast h)⟩

private noncomputable def classicalRationalClosePolynomialSet (A : ℕ) : Set ℚ[X] :=
  @closePolynomialSet ℚ (inferInstance : Field ℚ)
    (fun x y ↦ Classical.propDecidable (x = y)) 4 rationalEvaluationDomain (fun _ ↦ 0) 2 A

private theorem half_rate_threshold_lt_three_quarters :
    firstOrderRateThreshold (1 / 2 : ℝ) < 3 / 4 := by
  rw [firstOrderRateThreshold]
  have hroot : Real.sqrt (27 / 8 : ℝ) < 33 / 16 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 33 / 16)]
    norm_num
  rw [show (1 / 2 : ℝ) * (5 - 1 / 2) * (2 - 1 / 2) = 27 / 8 by norm_num]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 8 - 1 / 2)]
  nlinarith

open Classical in
/-- The complete list over `ℚ` is finite and contains the zero polynomial. -/
example :
    (classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4))).Finite ∧
      (0 : ℚ[X]) ∈ classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4)) := by
  obtain ⟨hfinite, _hraw, _hceil, _hclosed⟩ :=
    automaticFirstOrder_closePolynomialSet_at_ceil_finite_and_card_le
      (rho := 1 / 2) (a := 3 / 4) (n := 4) (k := 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      half_rate_threshold_lt_three_quarters (by norm_num : (3 / 4 : ℝ) < 1)
      (by norm_num : 0 < 4) (by norm_num : 2 ≤ 2)
      (by norm_num : (2 : ℝ) ≤ (1 / 2) * 4)
      rationalEvaluationDomain (fun _ ↦ 0)
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  change (classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4))).Finite at hfinite
  refine ⟨hfinite, ?_⟩
  unfold classicalRationalClosePolynomialSet closePolynomialSet
  simp only [Set.mem_ofPred_eq]
  exact ⟨WithBot.bot_lt_coe 2,
    by norm_num [polynomialAgreementSet, rationalEvaluationDomain]⟩

private def smallFirstOrderProfile :
    ReedSolomon.HiddenDerivative.CurveProfile.LineProfile :=
  { n := 2
    k := 2
    agreement := 2
    multiplicity := 2
    firstDerivativeCap := 0
    totalJetCap := 1
    batchingDegree := 1
    supportDimension := 7
    localRank := 3
    columnY₀Weight := 3
    height := 1
    heightSlots := 11 }

private def finiteEvaluationDomain : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), by
    intro i j h
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact Fin.ext (by exact_mod_cast h)⟩

/-- A verified profile bounds a concrete nonempty family of agreeing polynomials. -/
example :
    (({0} : Finset ℚ[X]).card : ℚ) ≤ tightListEnvelope smallFirstOrderProfile := by
  apply finiteListBound_of_profile (p := smallFirstOrderProfile) (by decide) rfl
    (by decide) (by decide) finiteEvaluationDomain (fun _ ↦ 0)
    (Or.inl ringChar.eq_zero)
  intro P hP
  have hPzero : P = 0 := by simpa using hP
  subst P
  constructor
  · simp
  · simp [smallFirstOrderProfile, finiteEvaluationDomain]
