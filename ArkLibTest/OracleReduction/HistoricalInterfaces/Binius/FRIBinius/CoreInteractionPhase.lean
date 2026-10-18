/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section
  -- The inferred composed protocol types contain public inline bounds proofs.


namespace Binius.FRIBinius.CoreInteractionPhase

noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold _root_.RingSwitching

open scoped NNReal

variable (κ : ℕ) [NeZero κ]

variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))]
  [hF₂ : Fact (Fintype.card K = 2)]

variable [Algebra K L]

variable (β : Basis (Fin (2 ^ κ)) K L) [h_β₀_eq_1 : Fact (β 0 = 1)]

variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡]
  [NeZero ϑ]

variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)

variable (h_l : ℓ = ℓ' + κ)

variable [hdiv : Fact (ϑ ∣ ℓ')]

section FinalSumcheckStep

theorem finalSumcheckOracleReduction_perfectCompleteness_historicalType
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness (pSpec :=
      BinaryBasefold.pSpecFinalSumcheckStep (L := L)) (relIn :=
      BinaryBasefold.strictRoundRelation (mp :=
        RingSwitching_BBFSumcheckMultParam κ L K (β :=
          booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)
        (Fin.last ℓ'))
      (relOut :=
      BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (oracleReduction :=
      finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) h_l)
      (init := init) (impl := impl) :=
  by historical_exact finalSumcheckOracleReduction_perfectCompleteness

assert_historical_type finalSumcheckOracleReduction_perfectCompleteness
  finalSumcheckOracleReduction_perfectCompleteness_historicalType

theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate
          h_l).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 :=
        boolEmbedding L) (mp :=
        RingSwitching_BBFSumcheckMultParam κ L K (booleanHypercubeBasis κ L K β)
          ℓ ℓ' h_l)
        (Fin.last ℓ'))
      (relOut :=
      BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError L) :=
  by historical_exact finalSumcheckOracleVerifier_rbrKnowledgeSoundness

assert_historical_type finalSumcheckOracleVerifier_rbrKnowledgeSoundness
  finalSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType

end FinalSumcheckStep

section CoreInteractionPhaseReduction

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem coreInteractionOracleReduction_perfectCompleteness_historicalType :
    OracleReduction.perfectCompleteness (oSpec := []ₒ) (pSpec :=
      BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (OStmtIn :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        (Fin.last ℓ'))
      (relIn :=
      RingSwitching.strictSumcheckRoundRelation κ (L := L) (K := K)
        (biniusProfile κ L K β) ℓ ℓ' h_l (aOStmtIn :=
        BinaryBasefoldAbstractOStmtIn (κ := κ) (L := L) (K := K) (β := β) (ℓ' :=
          ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        0)
      (relOut :=
      BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (oracleReduction :=
      coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) h_l)
      (init := init) (impl := impl) :=
  by historical_exact coreInteractionOracleReduction_perfectCompleteness

assert_historical_type coreInteractionOracleReduction_perfectCompleteness
  coreInteractionOracleReduction_perfectCompleteness_historicalType

theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness_historicalType :
    (coreInteractionOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' :=
          ℓ') (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate)).rbrKnowledgeSoundnessAveraged
      init impl (OStmtIn :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        (Fin.last ℓ'))
      (pSpec :=
      BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (relIn :=
      RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
        (aOStmtIn :=
        BinaryBasefoldAbstractOStmtIn (κ := κ) (L := L) (K := K) (β := β) (ℓ' :=
          ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        0)
      (relOut :=
      BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (rbrKnowledgeError :=
      coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact coreInteractionOracleVerifier_rbrKnowledgeSoundness

assert_historical_type coreInteractionOracleVerifier_rbrKnowledgeSoundness
  coreInteractionOracleVerifier_rbrKnowledgeSoundness_historicalType

end CoreInteractionPhaseReduction

end

end Binius.FRIBinius.CoreInteractionPhase
