/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.FiniteFieldBudget
import ArkLibExamples.ReedSolomon.ProveKit.Parameters
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact local ProveKit budgets

This module checks the integer arithmetic for every frozen ProveKit code round.  Each failure
phase is compared separately with `2^-128`, following the implementation generator's allocation;
the results do not assert a transcript-wide union bound.  They also do not supply a semantic MCA
or tensor-fold theorem.  Those coding statements belong in `Certificates.lean` and remain
separate from the numerical `(3E+2L)/q` calculation here.

Only the query-survival phase receives the existing inclusive PoW factor.  The budgets use the
original OOD counts and transition formulas, with the levelwise fold factor three.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open ArkLib.FiniteFieldBudget

/-- The complete numerical obligations for one committed code.  The semantic certificate and
tensor theorem are intentionally not fields of this arithmetic structure. -/
structure RoundBudget (r : CodeRound) (fieldSize security nonceSpace : ℕ) : Prop where
  structural : r.StructurallyValid fieldSize
  tensorFoldAndIdentity : TensorFoldIdentityMeetsTarget r.foldHeight r.exceptionalCount
    r.listSize fieldSize security
  oodSeparation : RepeatedOodMeetsTarget r.listSize r.coefficientsPerVector fieldSize
    r.oodSamples security
  querySurvival : QueryMeetsTarget nonceSpace r.powThreshold r.agreement r.n
    r.revisedQueries security

/-- Embed a transition number as its source row. -/
def sourceIndex {rounds : ℕ} (i : Fin (rounds - 1)) : Fin rounds :=
  ⟨i.val, by omega⟩

/-- Embed a transition number as its target row. -/
def targetIndex {rounds : ℕ} (i : Fin (rounds - 1)) : Fin rounds :=
  ⟨i.val + 1, by omega⟩

/-- Round-local budgets and every adjacent source-to-target list combination. -/
structure ScheduleBudget {rounds : ℕ} (s : Schedule rounds) : Prop where
  round : ∀ i, RoundBudget (s.row i) s.fieldSize s.security s.nonceSpace
  transition : ∀ i : Fin (rounds - 1),
    TransitionMeetsTarget (s.row (sourceIndex i)).revisedQueries
      (s.row (targetIndex i)).oodSamples (s.row (targetIndex i)).listSize
      s.fieldSize s.security

theorem passportOuterWitness_roundBudget (i : Fin 6) :
    RoundBudget (passportOuterWitness.row i) bn254FieldSize security nonceSpace := by
  fin_cases i <;> constructor <;>
    norm_num [passportOuterWitness, codeRound, powThreshold, bn254FieldSize, security, nonceSpace,
      CodeRound.StructurallyValid, TensorFoldIdentityMeetsTarget, RepeatedOodMeetsTarget,
      QueryMeetsTarget]

theorem passportOuterWitness_transitionBudget (i : Fin 5) :
    TransitionMeetsTarget
      (passportOuterWitness.row (sourceIndex i)).revisedQueries
      (passportOuterWitness.row (targetIndex i)).oodSamples
      (passportOuterWitness.row (targetIndex i)).listSize bn254FieldSize security := by
  fin_cases i <;>
    norm_num [passportOuterWitness, sourceIndex, targetIndex, codeRound, powThreshold,
      TransitionMeetsTarget, bn254FieldSize, security]

/-- Exact per-phase arithmetic for both identical Passport outer witnesses. -/
theorem passportOuterWitness_budget : ScheduleBudget passportOuterWitness where
  round := passportOuterWitness_roundBudget
  transition := passportOuterWitness_transitionBudget

theorem passportInternalZk_roundBudget (i : Fin 4) :
    RoundBudget (passportInternalZk.row i) bn254FieldSize security nonceSpace := by
  fin_cases i <;> constructor <;>
    norm_num [passportInternalZk, codeRound, powThreshold, bn254FieldSize, security, nonceSpace,
      CodeRound.StructurallyValid, TensorFoldIdentityMeetsTarget, RepeatedOodMeetsTarget,
      QueryMeetsTarget]

theorem passportInternalZk_transitionBudget (i : Fin 3) :
    TransitionMeetsTarget
      (passportInternalZk.row (sourceIndex i)).revisedQueries
      (passportInternalZk.row (targetIndex i)).oodSamples
      (passportInternalZk.row (targetIndex i)).listSize bn254FieldSize security := by
  fin_cases i <;>
    norm_num [passportInternalZk, sourceIndex, targetIndex, codeRound, powThreshold,
      TransitionMeetsTarget, bn254FieldSize, security]

/-- The initial two-vector line challenge has its own `E/q` phase. -/
theorem passportInternalZk_initialTwoVectorTransfer :
    LineTransferMeetsTarget (passportInternalZk.row 0).exceptionalCount
      bn254FieldSize security := by
  norm_num [LineTransferMeetsTarget, passportInternalZk, codeRound, powThreshold,
    bn254FieldSize, security]

/-- Evaluation RLC cancellation for the committed pair costs `1/q`. -/
theorem passportInternalZk_initialEvaluationCancellation :
    FieldCollisionMeetsTarget 1 bn254FieldSize security := by
  norm_num [FieldCollisionMeetsTarget, bn254FieldSize, security]

/-- The implementation allocates the initial line bad set and evaluation cancellation together
as `(E + 1)/q`; this grouped check accompanies the two constituent bounds above. -/
theorem passportInternalZk_initialLineAndEvaluation :
    FieldCollisionMeetsTarget ((passportInternalZk.row 0).exceptionalCount + 1)
      bn254FieldSize security := by
  norm_num [FieldCollisionMeetsTarget, passportInternalZk, codeRound, powThreshold,
    bn254FieldSize, security]

/-- The two linear forms and one OOD form share the separately sampled constraint RLC. -/
theorem passportInternalZk_initialConstraintRlc :
    FieldCollisionMeetsTarget 2 bn254FieldSize security := by
  norm_num [FieldCollisionMeetsTarget, bn254FieldSize, security]

/-- The unchanged final sumcheck identity is a separate `2/q` phase. -/
theorem passportInternalZk_finalIdentity :
    FieldCollisionMeetsTarget 2 bn254FieldSize security := by
  norm_num [FieldCollisionMeetsTarget, bn254FieldSize, security]

/-- The unchanged rho-zero/liveness event is a separate `1/q` phase. -/
theorem passportInternalZk_rhoNonzero :
    FieldCollisionMeetsTarget 1 bn254FieldSize security := by
  norm_num [FieldCollisionMeetsTarget, bn254FieldSize, security]

/-- Exact arithmetic for each of the two identical internal zkWHIR proofs. -/
theorem passportInternalZk_budget : ScheduleBudget passportInternalZk where
  round := passportInternalZk_roundBudget
  transition := passportInternalZk_transitionBudget

/-- The two outer witnesses have distinct initial constraint-combination counts, four and three. -/
theorem passportOuterWitness_initialConstraintRlc (i : Fin 2) :
    FieldCollisionMeetsTarget (![4, 3] i) bn254FieldSize security := by
  fin_cases i <;> norm_num [FieldCollisionMeetsTarget, bn254FieldSize, security]

theorem goldilocksLookupWitness_roundBudget (i : Fin 4) :
    RoundBudget (goldilocksLookupWitness.row i) goldilocksCubicFieldSize security nonceSpace := by
  fin_cases i <;> constructor <;>
    norm_num [goldilocksLookupWitness, codeRound, powThreshold, goldilocksCubicFieldSize, security,
      nonceSpace, CodeRound.StructurallyValid, TensorFoldIdentityMeetsTarget,
      RepeatedOodMeetsTarget, QueryMeetsTarget]

theorem goldilocksLookupWitness_transitionBudget (i : Fin 3) :
    TransitionMeetsTarget
      (goldilocksLookupWitness.row (sourceIndex i)).revisedQueries
      (goldilocksLookupWitness.row (targetIndex i)).oodSamples
      (goldilocksLookupWitness.row (targetIndex i)).listSize
      goldilocksCubicFieldSize security := by
  fin_cases i <;>
    norm_num [goldilocksLookupWitness, sourceIndex, targetIndex, codeRound, powThreshold,
      TransitionMeetsTarget, goldilocksCubicFieldSize, security]

/-- Exact arithmetic for both identical cubic-Goldilocks lookup witnesses. -/
theorem goldilocksLookupWitness_budget : ScheduleBudget goldilocksLookupWitness where
  round := goldilocksLookupWitness_roundBudget
  transition := goldilocksLookupWitness_transitionBudget

theorem goldilocksLookupBlind_roundBudget (i : Fin 1) :
    RoundBudget (goldilocksLookupBlind.row i) goldilocksCubicFieldSize security nonceSpace := by
  fin_cases i
  constructor <;>
    norm_num [goldilocksLookupBlind, codeRound, powThreshold, goldilocksCubicFieldSize, security,
      nonceSpace, CodeRound.StructurallyValid, TensorFoldIdentityMeetsTarget,
      RepeatedOodMeetsTarget, QueryMeetsTarget]

/-- The initial blinding code is a one-row schedule and therefore has no internal transition. -/
theorem goldilocksLookupBlind_budget : ScheduleBudget goldilocksLookupBlind where
  round := goldilocksLookupBlind_roundBudget
  transition := by intro i; exact Fin.elim0 i

/-- Transition from the 99-query initial blinding code to the fixed Johnson-list tail. -/
theorem goldilocksLookupBlindTail_transition :
    TransitionMeetsTarget (goldilocksLookupBlind.row 0).revisedQueries
      goldilocksLookupBlindTail.oodSamples goldilocksLookupBlindTail.listSize
      goldilocksCubicFieldSize security := by
  norm_num [TransitionMeetsTarget, goldilocksLookupBlind, goldilocksLookupBlindTail, codeRound,
    powThreshold, goldilocksCubicFieldSize, security]

/-- The tail's exact post-grinding query check retains the ratio `21/80` and 62 queries. -/
theorem goldilocksLookupBlindTail_query :
    QueryMeetsTarget nonceSpace goldilocksLookupBlindTail.powThreshold
      goldilocksLookupBlindTail.queryAgreement goldilocksLookupBlindTail.queryDomain
      goldilocksLookupBlindTail.queries security := by
  norm_num [QueryMeetsTarget, goldilocksLookupBlindTail, powThreshold, nonceSpace, security]

/-- One OOD sample separates every pair in the fixed tail list of size 160. -/
theorem goldilocksLookupBlindTail_ood :
    RepeatedOodMeetsTarget goldilocksLookupBlindTail.listSize
      goldilocksLookupBlindTail.coefficientsPerVector goldilocksCubicFieldSize
      goldilocksLookupBlindTail.oodSamples security := by
  norm_num [RepeatedOodMeetsTarget, goldilocksLookupBlindTail, goldilocksCubicFieldSize, security]

/-- The unchanged tail identity costs `2/q`. -/
theorem goldilocksLookupBlindTail_identity :
    FieldCollisionMeetsTarget 2 goldilocksCubicFieldSize security := by
  norm_num [FieldCollisionMeetsTarget, goldilocksCubicFieldSize, security]

end ArkLibExamples.ReedSolomon.ProveKit
