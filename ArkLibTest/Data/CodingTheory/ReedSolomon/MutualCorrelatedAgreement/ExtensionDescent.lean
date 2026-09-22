/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import Mathlib.FieldTheory.Finite.Extension

open Polynomial ReedSolomon

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2

private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The zero pair explaining the zero candidate descends from the four-element extension. -/
example :
    HasExactCorrelatedPair pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (RingHom.id (ZMod 2)) 1 0 0 := by
  classical
  refine HasExactCorrelatedPair.descend pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
    (algebraMap (ZMod 2) E₄) 1 0 0 ?_
  refine ⟨(0, 0), by simp, by simp, ?_, ?_⟩
  · simp [correlatedPairSpecialization]
  · ext i
    simp [polynomialAgreementSet, commonPolynomialAgreementSet]
