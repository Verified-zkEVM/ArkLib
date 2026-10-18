/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial Module
  TensorProduct Nat Matrix

open scoped NNReal ProbabilityTheory

open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase

noncomputable section

variable (κ : ℕ) [NeZero κ]

variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]

variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]

variable [Algebra K L]

variable (P : RingSwitchingProfile K L κ)

variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

variable (h_l : ℓ = ℓ' + κ)

variable (aOStmtIn : AbstractOStmtIn L ℓ')

section IteratedSumcheckStep

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {n : ℕ}
  {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] [NeZero κ] [NeZero ℓ] in
theorem iteratedSumcheckOracleReduction_perfectCompleteness_historicalType
    (i : Fin ℓ') :
    OracleReduction.perfectCompleteness (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction :=
      iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i) (init := init)
      (impl := impl) :=
  by historical_exact iteratedSumcheckOracleReduction_perfectCompleteness

assert_historical_type iteratedSumcheckOracleReduction_perfectCompleteness
  iteratedSumcheckOracleReduction_perfectCompleteness_historicalType

open scoped NNReal

section

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType
    [NoZeroDivisors L] (hUnique : aOStmtIn.Functional) (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn
          i).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc) (relOut :=
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun _ => roundKnowledgeError L ℓ' i) :=
  by historical_exact iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness

assert_historical_type iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness
  iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType

end

end IteratedSumcheckStep

section FinalSumcheckStep

omit [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] in
theorem finalSumcheckOracleReduction_perfectCompleteness_historicalType
    {σ : Type} (hCoord : CoordinateLaws P) (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness (pSpec := pSpecFinalSumcheck L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput) (oracleReduction :=
      finalSumcheckOracleReduction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      (init := init) (impl := impl) :=
  by historical_exact finalSumcheckOracleReduction_perfectCompleteness

assert_historical_type finalSumcheckOracleReduction_perfectCompleteness
  finalSumcheckOracleReduction_perfectCompleteness_historicalType

section

omit [Fintype K] [DecidableEq K] [SampleableType L] in
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType
    [NoZeroDivisors L] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (hCoord : CoordinateLaws P) :
    (finalSumcheckVerifier (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' :=
          ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ')) (relOut :=
      aOStmtIn.toRelInput) (rbrKnowledgeError := fun _ =>
      finalSumcheckRbrKnowledgeError (L := L)) :=
  by historical_exact finalSumcheckOracleVerifier_rbrKnowledgeSoundness

assert_historical_type finalSumcheckOracleVerifier_rbrKnowledgeSoundness
  finalSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType

end

end FinalSumcheckStep

section LargeFieldReduction

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem coreInteraction_perfectCompleteness_historicalType
    (hCoord : CoordinateLaws P) :
    OracleReduction.perfectCompleteness (oracleReduction :=
      coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn) (StmtIn :=
      Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
      (OStmtIn := aOStmtIn.OStmtIn) (StmtOut := MLPEvalStatement L ℓ')
      (OStmtOut := aOStmtIn.OStmtIn) (WitIn := SumcheckWitness L ℓ' 0)
      (WitOut := WitMLP L ℓ') (relIn :=
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0) (relOut :=
      aOStmtIn.toRelInput) (init := init) (impl := impl) :=
  by historical_exact coreInteraction_perfectCompleteness

assert_historical_type coreInteraction_perfectCompleteness
  coreInteraction_perfectCompleteness_historicalType

section

omit [Fintype K] [DecidableEq K] in
theorem coreInteraction_rbrKnowledgeSoundness_historicalType [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) (hUnique : aOStmtIn.Functional) :
    OracleVerifier.rbrKnowledgeSoundnessAveraged (verifier :=
      coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn) (StmtIn :=
      Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
      (OStmtIn := aOStmtIn.OStmtIn) (StmtOut := MLPEvalStatement L ℓ')
      (OStmtOut := aOStmtIn.OStmtIn) (WitIn := SumcheckWitness L ℓ' 0)
      (WitOut := WitMLP L ℓ') (init := init) (impl := impl) (relIn :=
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0) (relOut :=
      aOStmtIn.toRelInput) (rbrKnowledgeError :=
      coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ')) :=
  by historical_exact coreInteraction_rbrKnowledgeSoundness

assert_historical_type coreInteraction_rbrKnowledgeSoundness
  coreInteraction_rbrKnowledgeSoundness_historicalType

end

end LargeFieldReduction

end

end RingSwitching.SumcheckPhase
