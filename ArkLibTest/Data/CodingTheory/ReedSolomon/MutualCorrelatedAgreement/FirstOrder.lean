/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.CurveAgreement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

open Polynomial Finset ReedSolomon ReedSolomon.HiddenDerivative

private def curveDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def curveValues : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 0

/-- A zero received curve has exact power agreement outside a finite exceptional set. -/
example : ∃ z : ℚ, ∃ P : ℚ[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet curveDomain (powerBatchedWord curveValues z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues (RingHom.id ℚ) 1 z P := by
  classical
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (F := ℚ) (E := AlgebraicClosure ℚ) (D := 1) (A := 1) (m := 2) (M := 1)
      (μ := 1) (k := 1) (h := 1) (n := 1) (K := 2) (L := 1) (ell := 0)
      curveDomain curveValues (algebraMap ℚ (AlgebraicClosure ℚ))
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [firstOrderCurveShiftedRowSlotBound, firstOrderGradedRankBound,
        firstOrderGradedSourceCount, firstOrderCurveShiftedHeightSlotCount,
        Finset.sum_range_succ])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨z, 0, by simp, ?_, ?_⟩
  · have hset : polynomialAgreementSet curveDomain (powerBatchedWord curveValues z)
        (0 : ℚ[X]) = Finset.univ := by
      ext i
      simp [polynomialAgreementSet, powerBatchedWord, curveValues]
    rw [hset]
    simp
  · apply hgood z hz 0 (by simp)
    simp [polynomialAgreementSet, powerBatchedWord, curveValues]
