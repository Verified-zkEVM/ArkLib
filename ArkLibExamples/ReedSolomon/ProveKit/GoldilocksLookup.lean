/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.Certificates
import ArkLibExamples.ReedSolomon.ProveKit.Budgets
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement

/-!
# Cubic-Goldilocks lookup certificates

This capstone specializes the two lookup witnesses and the independent blinding proof to the
canonical cubic Goldilocks field.  It derives scalar list, exact-line, and height-three tensor
semantics row by row.  The fixed blind tail retains its own transition, OOD, query, and identity
theorems from `Budgets.lean`. The tensor theorem supplies semantic `3E` counting and the
finite-list theorem supplies scalar `L` counting; those results and the arithmetic checks for
`2L`, OOD, transitions, and auxiliary phases are not combined into one failure event.
-/

open Polynomial ReedSolomon
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.GoldilocksLookup

open ConcreteFields ArkLib.FiniteFieldBudget
open TensorMCA

noncomputable section

set_option maxRecDepth 4096

local instance : DecidableEq GoldilocksCubic := Classical.decEq _

theorem field_card : Fintype.card GoldilocksCubic = goldilocksCubicFieldSize := by
  rw [goldilocksCubic_card]
  norm_num [Goldilocks.fieldSize, goldilocksCubicFieldSize]

theorem witness_characteristic (i : Fin 4) :
    ringChar GoldilocksCubic = 0 ∨
      max ((goldilocksWitnessProfiles i).k - 1) (goldilocksWitnessProfiles i).totalJetCap <
        ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  fin_cases i
  · norm_num [goldilocksWitnessProfiles, passportInternalProfiles, Goldilocks.fieldSize]
  · norm_num [goldilocksWitnessProfiles, Goldilocks.fieldSize]
  · change max 15 114 < Goldilocks.fieldSize
    norm_num [Goldilocks.fieldSize]
  · change max 1 227 < Goldilocks.fieldSize
    norm_num [Goldilocks.fieldSize]

theorem blind_characteristic :
    ringChar GoldilocksCubic = 0 ∨
      max (goldilocksBlindProfile.k - 1) goldilocksBlindProfile.totalJetCap <
        ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  norm_num [goldilocksBlindProfile, Goldilocks.fieldSize]

/-- Scalar finite-list semantics for either lookup witness copy. -/
theorem witness_finiteList
    (_copy : Fin 2) (i : Fin 4)
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ GoldilocksCubic)
    (received : Fin (goldilocksWitnessProfiles i).n → GoldilocksCubic)
    (S : Finset GoldilocksCubic[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (goldilocksWitnessProfiles i).k
      (goldilocksWitnessProfiles i).agreement P) :
    (S.card : ℚ) ≤ (goldilocksLookupWitness.row i).listSize :=
  goldilocksWitness_finiteListBound i domain received (witness_characteristic i) S hS

theorem witness_line
    (_copy : Fin 2) (i : Fin 4)
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ GoldilocksCubic) :
    LineExactAgreementBound domain (goldilocksWitnessProfiles i).k
      (goldilocksWitnessProfiles i).agreement
      (goldilocksLookupWitness.row i).exceptionalCount := by
  apply goldilocksWitness_lineExactAgreement i domain
  exact (witness_characteristic i).imp_right fun h ↦ lt_of_le_of_lt (by
    exact max_le_max_right _ (by fin_cases i <;> decide)) h

theorem witness_tensorWitness
    (copy : Fin 2) (i : Fin 4)
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ GoldilocksCubic) :
    FullSetLevelWitness
      ((code domain (goldilocksWitnessProfiles i).k) ^⋈
        (Fin (goldilocksLookupWitness.row i).vectorCount))
      (goldilocksWitnessProfiles i).agreement
      (goldilocksLookupWitness.row i).exceptionalCount := by
  apply fullSetLevelWitness_interleaved_of_exactAgreement domain (witness_line copy i domain)
  · fin_cases i <;> decide
  · fin_cases i <;> decide

theorem witness_tensorBad_card_le
    (copy : Fin 2) (i : Fin 4)
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ GoldilocksCubic)
    (u : (Fin 3 → Bool) → Fin (goldilocksWitnessProfiles i).n →
      Fin (goldilocksLookupWitness.row i).vectorCount → GoldilocksCubic) :
    (tensorFoldBad (witness_tensorWitness copy i domain) u).card ≤
      3 * (goldilocksLookupWitness.row i).exceptionalCount *
        Fintype.card GoldilocksCubic ^ 2 := by
  apply interleavedRS_tensorFoldBad_card_le_heightThree domain (witness_line copy i domain)
  · fin_cases i <;> decide
  · fin_cases i <;> decide

theorem witness_localBudgets (_copy : Fin 2) : ScheduleBudget goldilocksLookupWitness :=
  goldilocksLookupWitness_budget

/-- Scalar finite-list semantics for the independent lookup blinding commitment. -/
theorem blind_finiteList
    (domain : Fin goldilocksBlindProfile.n ↪ GoldilocksCubic)
    (received : Fin goldilocksBlindProfile.n → GoldilocksCubic)
    (S : Finset GoldilocksCubic[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received goldilocksBlindProfile.k
      goldilocksBlindProfile.agreement P) :
    (S.card : ℚ) ≤ (goldilocksLookupBlind.row 0).listSize :=
  goldilocksBlind_finiteListBound domain received blind_characteristic S hS

theorem blind_line
    (domain : Fin goldilocksBlindProfile.n ↪ GoldilocksCubic) :
    LineExactAgreementBound domain goldilocksBlindProfile.k goldilocksBlindProfile.agreement
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  apply goldilocksBlind_lineExactAgreement domain
  exact blind_characteristic.imp_right fun h ↦ lt_of_le_of_lt (by decide) h

theorem blind_tensorWitness
    (domain : Fin goldilocksBlindProfile.n ↪ GoldilocksCubic) :
    FullSetLevelWitness
      ((code domain goldilocksBlindProfile.k) ^⋈
        (Fin (goldilocksLookupBlind.row 0).vectorCount))
      goldilocksBlindProfile.agreement (goldilocksLookupBlind.row 0).exceptionalCount := by
  apply fullSetLevelWitness_interleaved_of_exactAgreement domain (blind_line domain) <;> decide

theorem blind_tensorBad_card_le
    (domain : Fin goldilocksBlindProfile.n ↪ GoldilocksCubic)
    (u : (Fin 3 → Bool) → Fin goldilocksBlindProfile.n →
      Fin (goldilocksLookupBlind.row 0).vectorCount → GoldilocksCubic) :
    (tensorFoldBad (blind_tensorWitness domain) u).card ≤
      3 * (goldilocksLookupBlind.row 0).exceptionalCount *
        Fintype.card GoldilocksCubic ^ 2 := by
  apply interleavedRS_tensorFoldBad_card_le_heightThree domain (blind_line domain) <;> decide

theorem blind_localBudgets : ScheduleBudget goldilocksLookupBlind :=
  goldilocksLookupBlind_budget

end

end ArkLibExamples.ReedSolomon.ProveKit.GoldilocksLookup
