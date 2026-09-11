/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalParameters
import ArkLibExamples.ReedSolomon.ProveKit.Budgets
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact local budgets for the analytical ProveKit schedules

The checks below preserve the transcript order and the existing phase boundaries.  In particular,
`ScheduleBudget` checks each code round separately and each adjacent incoming-combination event
separately; it is not a transcript-wide union bound.  The measured schedules and their budget
theorems in `Budgets.lean` remain unchanged.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open ArkLib.FiniteFieldBudget

theorem passportOuterAnalytical_roundBudget (i : Fin 6) :
    RoundBudget (passportOuterAnalytical.row i) bn254FieldSize security nonceSpace := by
  fin_cases i
  · change RoundBudget (passportOuterWitness.row 0) bn254FieldSize security nonceSpace
    exact passportOuterWitness_roundBudget 0
  · change RoundBudget (passportOuterWitness.row 1) bn254FieldSize security nonceSpace
    exact passportOuterWitness_roundBudget 1
  · change RoundBudget (passportOuterWitness.row 2) bn254FieldSize security nonceSpace
    exact passportOuterWitness_roundBudget 2
  · change RoundBudget (passportOuterWitness.row 3) bn254FieldSize security nonceSpace
    exact passportOuterWitness_roundBudget 3
  · constructor <;>
      norm_num [passportOuterAnalytical, codeRound, powThreshold, bn254FieldSize, security,
        nonceSpace, CodeRound.StructurallyValid, TensorFoldIdentityMeetsTarget,
        RepeatedOodMeetsTarget, QueryMeetsTarget]
  · change RoundBudget (passportOuterWitness.row 5) bn254FieldSize security nonceSpace
    exact passportOuterWitness_roundBudget 5

theorem passportOuterAnalytical_transitionBudget (i : Fin 5) :
    TransitionMeetsTarget
      (passportOuterAnalytical.row (sourceIndex i)).revisedQueries
      (passportOuterAnalytical.row (targetIndex i)).oodSamples
      (passportOuterAnalytical.row (targetIndex i)).listSize bn254FieldSize security := by
  fin_cases i
  · change TransitionMeetsTarget
      (passportOuterWitness.row (sourceIndex 0)).revisedQueries
      (passportOuterWitness.row (targetIndex 0)).oodSamples
      (passportOuterWitness.row (targetIndex 0)).listSize bn254FieldSize security
    exact passportOuterWitness_transitionBudget 0
  · change TransitionMeetsTarget
      (passportOuterWitness.row (sourceIndex 1)).revisedQueries
      (passportOuterWitness.row (targetIndex 1)).oodSamples
      (passportOuterWitness.row (targetIndex 1)).listSize bn254FieldSize security
    exact passportOuterWitness_transitionBudget 1
  · change TransitionMeetsTarget
      (passportOuterWitness.row (sourceIndex 2)).revisedQueries
      (passportOuterWitness.row (targetIndex 2)).oodSamples
      (passportOuterWitness.row (targetIndex 2)).listSize bn254FieldSize security
    exact passportOuterWitness_transitionBudget 2
  · change TransitionMeetsTarget 29 1 180429296 bn254FieldSize security
    norm_num [TransitionMeetsTarget, bn254FieldSize, security]
  · change TransitionMeetsTarget 22 1 712536 bn254FieldSize security
    norm_num [TransitionMeetsTarget, bn254FieldSize, security]

/-- All local and adjacent-transition inequalities for both identical analytical outer
witnesses. -/
theorem passportOuterAnalytical_budget : ScheduleBudget passportOuterAnalytical where
  round := passportOuterAnalytical_roundBudget
  transition := passportOuterAnalytical_transitionBudget

/-- The unchanged grinding threshold accepts 22 fifth-row queries. -/
theorem passportOuterAnalytical_fifth_query :
    QueryMeetsTarget nonceSpace (passportOuterAnalytical.row 4).powThreshold
      (passportOuterAnalytical.row 4).agreement (passportOuterAnalytical.row 4).n 22 security :=
  (passportOuterAnalytical_roundBudget 4).querySurvival

/-- At the same agreement and grinding threshold, 21 fifth-row queries fail the local target. -/
theorem passportOuterAnalytical_fifth_query_minimal :
    QueryFailsTarget nonceSpace (passportOuterAnalytical.row 4).powThreshold
      (passportOuterAnalytical.row 4).agreement (passportOuterAnalytical.row 4).n 21 security := by
  change QueryFailsTarget nonceSpace 22342747603335828 394 16384 21 security
  norm_num [QueryFailsTarget, nonceSpace, security]

/-- The fifth row's tensor-fold/identity event uses `3E + 2L` with its analytical constants. -/
theorem passportOuterAnalytical_fifth_tensorFoldAndIdentity :
    TensorFoldIdentityMeetsTarget 3 40320140359804306 180429296 bn254FieldSize security :=
  (passportOuterAnalytical_roundBudget 4).tensorFoldAndIdentity

/-- One OOD sample suffices for the fifth analytical Passport list. -/
theorem passportOuterAnalytical_fifth_ood :
    RepeatedOodMeetsTarget 180429296 128 bn254FieldSize 1 security :=
  (passportOuterAnalytical_roundBudget 4).oodSeparation

/-- The incoming event for the fifth row retains the preceding row's 29-query transcript
position and uses the fifth row's one OOD sample and list size. -/
theorem passportOuterAnalytical_fifth_incoming :
    TransitionMeetsTarget 29 1 180429296 bn254FieldSize security :=
  passportOuterAnalytical_transitionBudget 3

/-- The two internal Passport schedules and all their auxiliary phase checks are unchanged. -/
theorem passportAnalyticalInternal_unchanged : ScheduleBudget passportInternalZk :=
  passportInternalZk_budget

theorem goldilocksLookupAnalytical_roundBudget (i : Fin 4) :
    RoundBudget (goldilocksLookupAnalytical.row i) goldilocksCubicFieldSize security
      nonceSpace := by
  fin_cases i
  · constructor <;>
      norm_num [goldilocksLookupAnalytical, codeRound, powThreshold, goldilocksCubicFieldSize,
        security, nonceSpace, CodeRound.StructurallyValid, TensorFoldIdentityMeetsTarget,
        RepeatedOodMeetsTarget, QueryMeetsTarget]
  · change RoundBudget (goldilocksLookupWitness.row 1) goldilocksCubicFieldSize security
      nonceSpace
    exact goldilocksLookupWitness_roundBudget 1
  · change RoundBudget (goldilocksLookupWitness.row 2) goldilocksCubicFieldSize security
      nonceSpace
    exact goldilocksLookupWitness_roundBudget 2
  · change RoundBudget (goldilocksLookupWitness.row 3) goldilocksCubicFieldSize security
      nonceSpace
    exact goldilocksLookupWitness_roundBudget 3

theorem goldilocksLookupAnalytical_transitionBudget (i : Fin 3) :
    TransitionMeetsTarget
      (goldilocksLookupAnalytical.row (sourceIndex i)).revisedQueries
      (goldilocksLookupAnalytical.row (targetIndex i)).oodSamples
      (goldilocksLookupAnalytical.row (targetIndex i)).listSize
      goldilocksCubicFieldSize security := by
  fin_cases i
  · norm_num [goldilocksLookupAnalytical, goldilocksLookupWitness, sourceIndex, targetIndex,
      codeRound, powThreshold, TransitionMeetsTarget, goldilocksCubicFieldSize, security]
  · change TransitionMeetsTarget
      (goldilocksLookupWitness.row (sourceIndex 1)).revisedQueries
      (goldilocksLookupWitness.row (targetIndex 1)).oodSamples
      (goldilocksLookupWitness.row (targetIndex 1)).listSize
      goldilocksCubicFieldSize security
    exact goldilocksLookupWitness_transitionBudget 1
  · change TransitionMeetsTarget
      (goldilocksLookupWitness.row (sourceIndex 2)).revisedQueries
      (goldilocksLookupWitness.row (targetIndex 2)).oodSamples
      (goldilocksLookupWitness.row (targetIndex 2)).listSize
      goldilocksCubicFieldSize security
    exact goldilocksLookupWitness_transitionBudget 2

/-- All local and adjacent-transition inequalities for both identical analytical lookup
witnesses. -/
theorem goldilocksLookupAnalytical_budget : ScheduleBudget goldilocksLookupAnalytical where
  round := goldilocksLookupAnalytical_roundBudget
  transition := goldilocksLookupAnalytical_transitionBudget

/-- One OOD sample suffices for the first analytical Goldilocks list. -/
theorem goldilocksLookupAnalytical_first_ood :
    RepeatedOodMeetsTarget 39721253 8192 goldilocksCubicFieldSize 1 security :=
  (goldilocksLookupAnalytical_roundBudget 0).oodSeparation

/-- The first Goldilocks tensor-fold/identity event uses its retained MCA count and independent
list count. -/
theorem goldilocksLookupAnalytical_first_tensorFoldAndIdentity :
    TensorFoldIdentityMeetsTarget 3 12566666451549204 39721253
      goldilocksCubicFieldSize security :=
  (goldilocksLookupAnalytical_roundBudget 0).tensorFoldAndIdentity

/-- The measured and analytical Goldilocks schedules are kept distinct at the first OOD count. -/
theorem goldilocksLookup_measured_and_analytical_ood :
    (goldilocksLookupWitness.row 0).oodSamples = 2 ∧
      (goldilocksLookupAnalytical.row 0).oodSamples = 1 := by
  constructor <;> rfl

/-- The lookup blinding schedule and terminal checks remain the existing measured ones. -/
theorem goldilocksLookupAnalyticalBlind_unchanged : ScheduleBudget goldilocksLookupBlind :=
  goldilocksLookupBlind_budget

end ArkLibExamples.ReedSolomon.ProveKit
