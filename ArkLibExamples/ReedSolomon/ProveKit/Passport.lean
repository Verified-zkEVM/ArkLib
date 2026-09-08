/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.Certificates
import ArkLibExamples.ReedSolomon.ProveKit.Budgets
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement

/-!
# Passport ProveKit certificates

This capstone specializes the frozen outer and internal schedules to the canonical BN254 scalar
field. Each theorem concerns one row and one failure phase. The `copy : Fin 2` parameter indexes
the two intended outer invocations and the two intended internal invocations; it does not assert
that the protocol makes those invocations or that their randomness is independent.

The tensor theorems use `vectorCount` as the row-wise interleaving width.  The separate
`foldWidth = 8` is represented by the height-three binary tensor, whose three challenge levels
give the factor in the exact arithmetic budget. The tensor theorem supplies semantic
`3E` counting and the finite-list theorem supplies scalar `L` counting. The arithmetic checks for
`2L`, OOD, transitions, and auxiliary phases are not assembled here into a single failure event.
-/

open Polynomial ReedSolomon
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.Passport

open ConcreteFields ArkLib.FiniteFieldBudget
open TensorMCA

noncomputable section

set_option maxRecDepth 4096

universe u

theorem field_card : Fintype.card BN254Scalar = bn254FieldSize := by
  rw [bn254Scalar_card]
  norm_num [BN254.scalarFieldSize, bn254FieldSize]

theorem outer_characteristic (i : Fin 6) :
    ringChar BN254Scalar = 0 ∨
      max ((passportOuterProfiles i).k - 1) (passportOuterProfiles i).totalJetCap <
        ringChar BN254Scalar := by
  right
  rw [bn254Scalar_ringChar]
  fin_cases i <;> norm_num [passportOuterProfiles, BN254.scalarFieldSize]

theorem internal_characteristic (i : Fin 4) :
    ringChar BN254Scalar = 0 ∨
      max ((passportInternalProfiles i).k - 1) (passportInternalProfiles i).totalJetCap <
        ringChar BN254Scalar := by
  right
  rw [bn254Scalar_ringChar]
  fin_cases i <;> norm_num [passportInternalProfiles, BN254.scalarFieldSize]

/-- Scalar finite-list semantics for either outer witness copy. -/
theorem outer_finiteList
    (_copy : Fin 2) (i : Fin 6)
    (domain : Fin (passportOuterProfiles i).n ↪ BN254Scalar)
    (received : Fin (passportOuterProfiles i).n → BN254Scalar)
    (S : Finset BN254Scalar[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (passportOuterProfiles i).k
      (passportOuterProfiles i).agreement P) :
    (S.card : ℚ) ≤ (passportOuterWitness.row i).listSize :=
  passportOuter_finiteListBound i domain received (outer_characteristic i) S hS

/-- Exact scalar line semantics for either outer witness copy. -/
theorem outer_line
    (_copy : Fin 2) (i : Fin 6)
    (domain : Fin (passportOuterProfiles i).n ↪ BN254Scalar) :
    LineExactAgreementBound domain (passportOuterProfiles i).k
      (passportOuterProfiles i).agreement (passportOuterWitness.row i).exceptionalCount := by
  apply passportOuter_lineExactAgreement i domain
  exact (outer_characteristic i).imp_right fun h ↦ lt_of_le_of_lt (by
    exact max_le_max_right _ (by fin_cases i <;> decide)) h

/-- The actual interleaving width in an outer row inherits its derived scalar line witness. -/
theorem outer_tensorWitness
    (copy : Fin 2) (i : Fin 6)
    (domain : Fin (passportOuterProfiles i).n ↪ BN254Scalar) :
    FullSetLevelWitness
      ((code domain (passportOuterProfiles i).k) ^⋈
        (Fin (passportOuterWitness.row i).vectorCount))
      (passportOuterProfiles i).agreement (passportOuterWitness.row i).exceptionalCount := by
  apply fullSetLevelWitness_interleaved_of_exactAgreement domain (outer_line copy i domain)
  · fin_cases i <;> decide
  · fin_cases i <;> decide

/-- Height-three tensor folding has at most seven copies of the derived bad-line set. -/
theorem outer_tensorBad_card_le
    (copy : Fin 2) (i : Fin 6)
    (domain : Fin (passportOuterProfiles i).n ↪ BN254Scalar)
    (u : (Fin 3 → Bool) → Fin (passportOuterProfiles i).n →
      Fin (passportOuterWitness.row i).vectorCount → BN254Scalar) :
    (tensorFoldBad (outer_tensorWitness copy i domain) u).card ≤
      3 * (passportOuterWitness.row i).exceptionalCount * Fintype.card BN254Scalar ^ 2 := by
  apply interleavedRS_tensorFoldBad_card_le_heightThree domain (outer_line copy i domain)
  · fin_cases i <;> decide
  · fin_cases i <;> decide

/-- Each indexed outer invocation satisfies the same round-local and transition arithmetic.
The separately named copy-dependent initial constraint checks, with RLC counts `[4, 3]`, remain
outside `ScheduleBudget`. -/
theorem outer_localBudgets (_copy : Fin 2) : ScheduleBudget passportOuterWitness :=
  passportOuterWitness_budget

/-- Scalar finite-list semantics for either internal proof copy. -/
theorem internal_finiteList
    (_copy : Fin 2) (i : Fin 4)
    (domain : Fin (passportInternalProfiles i).n ↪ BN254Scalar)
    (received : Fin (passportInternalProfiles i).n → BN254Scalar)
    (S : Finset BN254Scalar[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (passportInternalProfiles i).k
      (passportInternalProfiles i).agreement P) :
    (S.card : ℚ) ≤ (passportInternalZk.row i).listSize :=
  passportInternal_finiteListBound i domain received (internal_characteristic i) S hS

/-- Exact scalar line semantics for either internal proof copy. -/
theorem internal_line
    (_copy : Fin 2) (i : Fin 4)
    (domain : Fin (passportInternalProfiles i).n ↪ BN254Scalar) :
    LineExactAgreementBound domain (passportInternalProfiles i).k
      (passportInternalProfiles i).agreement (passportInternalZk.row i).exceptionalCount := by
  apply passportInternal_lineExactAgreement i domain
  exact (internal_characteristic i).imp_right fun h ↦ lt_of_le_of_lt (by
    exact max_le_max_right _ (by fin_cases i <;> decide)) h

theorem internal_tensorWitness
    (copy : Fin 2) (i : Fin 4)
    (domain : Fin (passportInternalProfiles i).n ↪ BN254Scalar) :
    FullSetLevelWitness
      ((code domain (passportInternalProfiles i).k) ^⋈
        (Fin (passportInternalZk.row i).vectorCount))
      (passportInternalProfiles i).agreement (passportInternalZk.row i).exceptionalCount := by
  apply fullSetLevelWitness_interleaved_of_exactAgreement domain (internal_line copy i domain)
  · fin_cases i <;> decide
  · fin_cases i <;> decide

theorem internal_tensorBad_card_le
    (copy : Fin 2) (i : Fin 4)
    (domain : Fin (passportInternalProfiles i).n ↪ BN254Scalar)
    (u : (Fin 3 → Bool) → Fin (passportInternalProfiles i).n →
      Fin (passportInternalZk.row i).vectorCount → BN254Scalar) :
    (tensorFoldBad (internal_tensorWitness copy i domain) u).card ≤
      3 * (passportInternalZk.row i).exceptionalCount * Fintype.card BN254Scalar ^ 2 := by
  apply interleavedRS_tensorFoldBad_card_le_heightThree domain (internal_line copy i domain)
  · fin_cases i <;> decide
  · fin_cases i <;> decide

/-- Each indexed internal invocation satisfies the same round-local and transition arithmetic.
The separately named initial line/evaluation grouping, initial constraint RLC, final identity,
and rho-nonzero checks remain outside `ScheduleBudget` and retain their phase boundaries in
`Budgets.lean`. -/
theorem internal_localBudgets (_copy : Fin 2) : ScheduleBudget passportInternalZk :=
  passportInternalZk_budget

end

end ArkLibExamples.ReedSolomon.ProveKit.Passport
