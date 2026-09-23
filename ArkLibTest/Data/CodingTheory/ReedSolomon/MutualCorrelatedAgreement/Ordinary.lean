/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorAssembly
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget

open ReedSolomon

open scoped BigOperators

private abbrev assemblyPoly := MvPolynomial (Fin 1) ℚ

private noncomputable def assemblyEval : Unit → Unit → (assemblyPoly →+* assemblyPoly) :=
  fun _ _ ↦ RingHom.id _

private def assemblyHeight : assemblyPoly → ℕ := fun _ ↦ 0

example : ∃ ex : Finset Unit, (ex.card : ℚ) ≤ ordinaryFactorRaw 0 1 0 1 0 ∧
    ∀ w ∉ ex, ∀ v, assemblyEval w v (1 : assemblyPoly) = 0 → False := by
  apply exists_exceptional_ordinaryFactorAssembly (i := 0) (Q := 1) one_ne_zero assemblyEval
    (fun _ _ ↦ False) assemblyHeight 0 1 0 1 0 (by norm_num) (by norm_num) (by simp)
  · simp [assemblyHeight, MvPolynomial.positiveDegreeFactorClasses]
  · refine ⟨∅, by simp [assemblyHeight], ?_⟩
    intro w _ v
    simp [assemblyEval, MvPolynomial.radicalContent]
  · intro c hc
    simp [MvPolynomial.positiveDegreeFactorClasses] at hc

example : ordinaryFrobeniusMixedDegree 1 1 2 2 ≤ 2 * 2 + ordinaryPsi 1 4 :=
  ordinaryFrobeniusMixedDegree_le_unified 1 1 2 2
