/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveProfile
import ArkLibExamples.ReedSolomon.ProveKit.Certificates
import ArkLibExamples.ReedSolomon.ZisK.Interpolation
import ArkLibExamples.ReedSolomon.LambdaVM.Certificates

/-!
# Application migration to optimized hybrid curve recovery

The application profiles retain their independently proved squarefree recovery theorem and add
optimized hybrid recovery.  Their new semantic envelope is the minimum of those two proved
bounds, so it is automatically no worse than every existing squarefree application budget.

The ProveKit exceptional counts were conservatively stored from the older curve expression.  We
record exact ceiling equalities for that literal legacy expression separately; unlike the ZisK
and LambdaVM tables, they are not claimed to be exact ceilings of the smaller squarefree bound.
-/

open Polynomial ReedSolomon

namespace ArkLibExamples.ReedSolomon.CurveMigration

open _root_.ReedSolomon.CurveCertificate

noncomputable section

set_option maxRecDepth 4096

universe u

open Classical in
private theorem exists_exceptional_best_le_budget
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : _root_.ReedSolomon.CurveProfile.LineProfile}
    (hp : p.CurveVerification)
    (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (hbudget : bestCurveEnvelope p split ≤ (budget : ℝ))
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max p.D p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      exceptional.card ≤ budget ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exact_powerAgreement_best hp split hsplit hk hell hM hMB
      domain values iota hchar
  refine ⟨exceptional, ?_, hgood⟩
  exact_mod_cast hcard.trans hbudget

/-! ## ProveKit -/

namespace ProveKit

open ArkLibExamples.ReedSolomon.ProveKit

/-- The retained squarefree alternative is below every stored Passport-outer budget. -/
theorem passportOuter_squarefree_envelopes_le (i : Fin 6) :
    squarefreeSharpCurveEnvelope (passportOuterProfiles i) (passportOuterSplits i) ≤
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The retained squarefree alternative is below every stored Passport-internal budget. -/
theorem passportInternal_squarefree_envelopes_le (i : Fin 4) :
    squarefreeSharpCurveEnvelope (passportInternalProfiles i) (passportInternalSplits i) ≤
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The retained squarefree alternative is below every stored lookup-witness budget. -/
theorem goldilocksWitness_squarefree_envelopes_le (i : Fin 4) :
    squarefreeSharpCurveEnvelope (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i) ≤
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The retained squarefree alternative is below the stored lookup-blinding budget. -/
theorem goldilocksBlind_squarefree_envelope_le :
    squarefreeSharpCurveEnvelope goldilocksBlindProfile goldilocksBlindSplit ≤
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

/-- The stored Passport-outer counts are exact ceilings of their literal legacy expression. -/
theorem passportOuter_legacy_envelope_ceiling_eq (i : Fin 6) :
    ⌈envelope (passportOuterProfiles i) (passportOuterSplits i)⌉₊ =
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The stored Passport-internal counts are exact ceilings of their literal legacy expression. -/
theorem passportInternal_legacy_envelope_ceiling_eq (i : Fin 4) :
    ⌈envelope (passportInternalProfiles i) (passportInternalSplits i)⌉₊ =
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The stored lookup-witness counts are exact ceilings of their literal legacy expression. -/
theorem goldilocksWitness_legacy_envelope_ceiling_eq (i : Fin 4) :
    ⌈envelope (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i)⌉₊ =
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The stored lookup-blinding count is the exact ceiling of its literal legacy expression. -/
theorem goldilocksBlind_legacy_envelope_ceiling_eq :
    ⌈envelope goldilocksBlindProfile goldilocksBlindSplit⌉₊ =
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

theorem passportOuter_best_envelopes_le (i : Fin 6) :
    bestCurveEnvelope (passportOuterProfiles i) (passportOuterSplits i) ≤
      ((passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast passportOuter_squarefree_envelopes_le i

theorem passportInternal_best_envelopes_le (i : Fin 4) :
    bestCurveEnvelope (passportInternalProfiles i) (passportInternalSplits i) ≤
      ((passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast passportInternal_squarefree_envelopes_le i

theorem goldilocksWitness_best_envelopes_le (i : Fin 4) :
    bestCurveEnvelope (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i) ≤
      ((goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast goldilocksWitness_squarefree_envelopes_le i

theorem goldilocksBlind_best_envelope_le :
    bestCurveEnvelope goldilocksBlindProfile goldilocksBlindSplit ≤
      ((goldilocksLookupBlind.row 0).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast goldilocksBlind_squarefree_envelope_le

open Classical in
/-- Optimized-hybrid-or-squarefree exact recovery for every Passport outer row. -/
theorem passportOuter_exists_exceptional_best
    (i : Fin 6) {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (values : Fin ((passportOuterProfiles i).batchingDegree + 1) →
      Fin (passportOuterProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      exceptional.card ≤
          (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportOuterProfiles i).k →
        (passportOuterProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportOuterProfiles i).k z P := by
  apply exists_exceptional_best_le_budget
    (passportOuterProfiles_verified i) (passportOuterSplits i)
    (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (passportOuterSplits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (passportOuter_best_envelopes_le i) domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

open Classical in
/-- Optimized-hybrid-or-squarefree exact recovery for every Passport internal row. -/
theorem passportInternal_exists_exceptional_best
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (values : Fin ((passportInternalProfiles i).batchingDegree + 1) →
      Fin (passportInternalProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      exceptional.card ≤
          (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportInternalProfiles i).k →
        (passportInternalProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportInternalProfiles i).k z P := by
  apply exists_exceptional_best_le_budget
    (passportInternalProfiles_verified i) (passportInternalSplits i)
    (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount
    (passportInternalSplits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (passportInternal_best_envelopes_le i) domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

open Classical in
/-- Optimized-hybrid-or-squarefree exact recovery for every lookup-witness row. -/
theorem goldilocksWitness_exists_exceptional_best
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (values : Fin ((goldilocksWitnessProfiles i).batchingDegree + 1) →
      Fin (goldilocksWitnessProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      exceptional.card ≤
          (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (goldilocksWitnessProfiles i).k →
        (goldilocksWitnessProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (goldilocksWitnessProfiles i).k z P := by
  apply exists_exceptional_best_le_budget
    (goldilocksWitnessProfiles_verified i) (goldilocksWitnessSplits i)
    (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (goldilocksWitnessSplits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (goldilocksWitness_best_envelopes_le i) domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

open Classical in
/-- Optimized-hybrid-or-squarefree exact recovery for the lookup-blinding row. -/
theorem goldilocksBlind_exists_exceptional_best
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (values : Fin (goldilocksBlindProfile.batchingDegree + 1) →
      Fin goldilocksBlindProfile.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      exceptional.card ≤ (goldilocksLookupBlind.row 0).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < goldilocksBlindProfile.k →
        goldilocksBlindProfile.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          goldilocksBlindProfile.k z P := by
  apply exists_exceptional_best_le_budget goldilocksBlindProfile_verified
    goldilocksBlindSplit (goldilocksLookupBlind.row 0).exceptionalCount
    goldilocksBlindSplit_admissible (by decide) (by decide) (by decide) (by decide)
    goldilocksBlind_best_envelope_le domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

end ProveKit

/-! ## ZisK -/

namespace ZisK

open ArkLibExamples.ReedSolomon.ZisK

/-- The generated ZisK counts are exact ceilings of the retained squarefree expressions. -/
theorem squarefree_envelope_ceiling_eq (i : Fin 8) :
    ⌈squarefreeSharpCurveEnvelope (profiles i) (splits i)⌉₊ = exceptionalCounts i := by
  fin_cases i <;> decide +kernel

theorem best_envelopes_le (i : Fin 8) :
    bestCurveEnvelope (profiles i) (splits i) ≤ (exceptionalCounts i : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast envelopes_le i

open Classical in
/-- Optimized-hybrid-or-squarefree exact recovery for every compressed ZisK curve. -/
theorem exists_exceptional_best (i : Fin 8)
    (domain : Fin (profiles i).n ↪ ConcreteFields.GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → ConcreteFields.GoldilocksCubic) :
    ∃ exceptional : Finset ConcreteFields.GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : ConcreteFields.GoldilocksCubic[X],
        P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id ConcreteFields.GoldilocksCubic)
          (profiles i).k z P := by
  apply exists_exceptional_best_le_budget (profiles_verified i) (splits i)
    (exceptionalCounts i) (splits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (best_envelopes_le i) domain values
    (algebraMap ConcreteFields.GoldilocksCubic
      (AlgebraicClosure ConcreteFields.GoldilocksCubic))
  exact Or.inr (by
    simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using
      characteristic_admissible i)

end ZisK

/-! ## LambdaVM -/

namespace LambdaVM

open ArkLibExamples.ReedSolomon.LambdaVM.CPU

/-- The generated LambdaVM counts are exact ceilings of the retained squarefree expressions. -/
theorem squarefree_envelope_ceiling_eq (i : Fin 9) :
    ⌈squarefreeSharpCurveEnvelope (profiles i) (splits i)⌉₊ = exceptionalCounts i := by
  fin_cases i <;> decide +kernel

theorem best_envelopes_le (i : Fin 9) :
    bestCurveEnvelope (profiles i) (splits i) ≤ (exceptionalCounts i : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast envelopes_le i

open Classical in
/-- Optimized-hybrid-or-squarefree exact recovery for every LambdaVM CPU curve. -/
theorem exists_exceptional_best (i : Fin 9)
    (domain : Fin (profiles i).n ↪ ConcreteFields.GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → ConcreteFields.GoldilocksCubic) :
    ∃ exceptional : Finset ConcreteFields.GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : ConcreteFields.GoldilocksCubic[X],
        P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id ConcreteFields.GoldilocksCubic)
          (profiles i).k z P := by
  apply exists_exceptional_best_le_budget (profiles_verified i) (splits i)
    (exceptionalCounts i) (splits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (best_envelopes_le i) domain values
    (algebraMap ConcreteFields.GoldilocksCubic
      (AlgebraicClosure ConcreteFields.GoldilocksCubic))
  exact Or.inr (by
    simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using
      curve_characteristic_admissible i)

end LambdaVM

end

end ArkLibExamples.ReedSolomon.CurveMigration
