/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial Module
  TensorProduct Nat Matrix

open scoped NNReal ProbabilityTheory

open ProbabilityTheory

open Sumcheck.Structured

noncomputable section

namespace RingSwitching.BatchingPhase

variable (κ : ℕ) [NeZero κ]

variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]

variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]

variable [Algebra K L]

variable (P : RingSwitchingProfile K L κ)

variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

variable (h_l : ℓ = ℓ' + κ)

variable (aOStmtIn : AbstractOStmtIn L ℓ')

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
theorem batchingReduction_perfectCompleteness_historicalType
    (hCoord : CoordinateLaws P) [IsDomain K] [NoZeroDivisors L] :
    OracleReduction.perfectCompleteness (oracleReduction :=
      batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)) (relIn :=
      batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn) (relOut :=
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0) (init := init) (impl :=
      impl) :=
  by historical_exact batchingReduction_perfectCompleteness

assert_historical_type batchingReduction_perfectCompleteness
  batchingReduction_perfectCompleteness_historicalType

omit [Fintype K] [DecidableEq K] in
omit [NeZero κ] [NeZero ℓ'] in
theorem batchingOracleVerifier_rbrKnowledgeSoundness_historicalType
    (hCoord : CoordinateLaws P) (hUnique : aOStmtIn.Functional) [IsDomain K]
    [NoZeroDivisors L] :
    OracleVerifier.rbrKnowledgeSoundnessAveraged (verifier :=
      oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)) (init := init)
      (impl := impl) (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (rbrKnowledgeError :=
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P)) :=
  by historical_exact batchingOracleVerifier_rbrKnowledgeSoundness

assert_historical_type batchingOracleVerifier_rbrKnowledgeSoundness
  batchingOracleVerifier_rbrKnowledgeSoundness_historicalType

end BatchingPhase

end RingSwitching
