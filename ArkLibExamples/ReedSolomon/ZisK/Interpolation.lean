/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.ZisK.Parameters
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Exact recovery for the compressed final STARK curves

For each positive-degree batching or folding curve, the finite support constructs
an interpolation equation. The sharp exceptional-fiber theorem then constructs one
exceptional set, uniformly for every close candidate, over cubic Goldilocks itself.
Neither a recovery assumption nor an exceptional-set bound is an input.
-/
open Polynomial ReedSolomon
namespace ArkLibExamples.ReedSolomon.ZisK
open ConcreteFields _root_.ReedSolomon.CurveProfile
open _root_.ReedSolomon.CurveCertificate
noncomputable section

/-- Every split is in the admissible interval between dimension and agreement. -/
theorem splits_admissible (i : Fin 8) :
    (profiles i).k ≤ splits i ∧ splits i ≤ (profiles i).agreement ∧
      (profiles i).agreement ≤ (profiles i).n := by
  fin_cases i <;> decide

/-- The sharp rational geometric bounds lie below the stated integer ceilings. -/
theorem envelopes_le (i : Fin 8) :
    _root_.ReedSolomon.CurveCertificate.squarefreeSharpCurveEnvelope
      (profiles i) (splits i) ≤ exceptionalCounts i := by
  fin_cases i <;> decide +kernel

/-- Goldilocks characteristic exceeds every candidate degree and derivative cap used here. -/
theorem characteristic_admissible (i : Fin 8) :
    max ((profiles i).k - 1) (profiles i).firstDerivativeCap <
      ringChar GoldilocksCubic := by
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [profiles, Goldilocks.fieldSize]

open Classical in
/-- Every row constructs an actual exceptional set and exact powers recovery outside it. -/
theorem exists_exceptional (i : Fin 8)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) → Fin (profiles i).n → GoldilocksCubic) :
    ∃ exceptional : Finset GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : GoldilocksCubic[X], P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic) (profiles i).k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exact_powerAgreement_squarefree_sharp_le
      (profiles_verified i)
      (splits i) (exceptionalCounts i) (splits_admissible i)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (envelopes_le i) domain values
      (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
      (Or.inr (characteristic_admissible i))
  exact ⟨exceptional, by exact_mod_cast hcard, hgood⟩

end
end ArkLibExamples.ReedSolomon.ZisK
