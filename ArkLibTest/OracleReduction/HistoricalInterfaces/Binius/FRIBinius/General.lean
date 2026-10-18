/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.FRIBinius.General
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

namespace Binius.FRIBinius.FullFRIBinius

noncomputable section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset
  AdditiveNTT Module Binius

open Binius.BinaryBasefold _root_.RingSwitching

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

section Pspec

end Pspec

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem fullOracleReduction_perfectCompleteness_historicalType :
    OracleProof.perfectCompleteness (oracleProof :=
      fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) h_l)
      (relation :=
      BatchingPhase.strictBatchingInputRelation κ L K (biniusProfile κ L K β) ℓ
        ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
      (init := init) (impl := impl) :=
  by historical_exact fullOracleReduction_perfectCompleteness

assert_historical_type fullOracleReduction_perfectCompleteness
  fullOracleReduction_perfectCompleteness_historicalType

open scoped NNReal

open FRIBinius.CoreInteractionPhase in
theorem batchingCoreVerifier_rbrKnowledgeSoundness_historicalType :
    (batchingCoreVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate
          h_l).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
        (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
      (relOut :=
      BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (rbrKnowledgeError :=
      batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) :=
  by historical_exact batchingCoreVerifier_rbrKnowledgeSoundness

assert_historical_type batchingCoreVerifier_rbrKnowledgeSoundness
  batchingCoreVerifier_rbrKnowledgeSoundness_historicalType

theorem fullOracleVerifier_rbrKnowledgeSoundness_historicalType :
    (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate) h_l).rbrKnowledgeSoundnessAveraged
      (Oₛₒ := fun i : Empty => nomatch i) init impl (relIn :=
      BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
        (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
      (relOut := acceptRejectOracleRel) (rbrKnowledgeError :=
      fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact fullOracleVerifier_rbrKnowledgeSoundness

assert_historical_type fullOracleVerifier_rbrKnowledgeSoundness
  fullOracleVerifier_rbrKnowledgeSoundness_historicalType

theorem fullOracleVerifier_knowledgeSoundness_historicalType :
    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
          (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate :=
            h_ℓ_add_R_rate) h_l)).knowledgeSoundness
      init impl (relIn :=
      BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
        (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
      (relOut := acceptRejectOracleRel) (knowledgeError :=
      concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions) :=
  by historical_exact fullOracleVerifier_knowledgeSoundness

assert_historical_type fullOracleVerifier_knowledgeSoundness
  fullOracleVerifier_knowledgeSoundness_historicalType

end

end Binius.FRIBinius.FullFRIBinius
