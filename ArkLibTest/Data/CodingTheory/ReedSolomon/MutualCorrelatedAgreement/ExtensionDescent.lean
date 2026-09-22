/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import Mathlib.FieldTheory.Finite.Extension

open Polynomial ReedSolomon

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2

noncomputable section

local instance : DecidableEq E₄ := Classical.decEq E₄

private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- A nonzero affine line and its candidate descend with their one-point agreement set. -/
example :
    HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
      (RingHom.id (ZMod 2)) 2 1 (1 + X) ∧
    polynomialAgreementSet pointDomain (fun _ ↦ (1 : ZMod 2)) (1 + X) = {0} ∧
    polynomialAgreementSet (pointDomain.trans ⟨algebraMap (ZMod 2) E₄,
      (algebraMap (ZMod 2) E₄).injective⟩)
      (fun _ ↦ algebraMap (ZMod 2) E₄ 1 + algebraMap (ZMod 2) E₄ 1 *
        algebraMap (ZMod 2) E₄ 0) ((1 + X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) =
        {0} := by
  classical
  let ι : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
  have hext : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
      ι 2 (ι 1) ((1 + X : (ZMod 2)[X]).map ι) := by
    refine ⟨(1, X), by norm_num, by norm_num, ?_, ?_⟩
    · simp [correlatedPairSpecialization]
    · ext i
      fin_cases i
      simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]
  refine ⟨HasExactCorrelatedPair.descend pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    ι 2 1 (1 + X) hext, ?_, ?_⟩
  · ext i
    fin_cases i
    simp [polynomialAgreementSet, pointDomain]
    rfl
  · ext i
    fin_cases i
    simp [polynomialAgreementSet, pointDomain]
    rfl

end
