/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase.SumcheckFold
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section


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

section FixFirstBridge

variable {L' : Type} [CommRing L'] {ℓ'' : ℕ}

end FixFirstBridge

section SumcheckFold

section Security

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}
    -- Completeness instance for the context lens


omit h_β₀_eq_1 in
theorem sumcheckFoldOracleReduction_perfectCompleteness_historicalType :
    OracleReduction.perfectCompleteness (oSpec := []ₒ) (StmtIn :=
      Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
      (OStmtIn :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (WitIn := RingSwitching.SumcheckWitness L ℓ' 0) (StmtOut :=
      Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
        (Fin.last ℓ'))
      (OStmtOut :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        (Fin.last ℓ'))
      (WitOut :=
      BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
        (Fin.last ℓ'))
      (pSpec :=
      BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn :=
      RingSwitching.strictSumcheckRoundRelation κ L K (biniusProfile κ L K β) ℓ
        ℓ' h_l (aOStmtIn :=
        BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate))
        0)
      (relOut :=
      BinaryBasefold.strictRoundRelation (mp :=
        RingSwitching_BBFSumcheckMultParam κ L K (β :=
          booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)
        (Fin.last ℓ'))
      (oracleReduction :=
      sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) h_l)
      (init := init) (impl := impl) :=
  by historical_exact sumcheckFoldOracleReduction_perfectCompleteness

assert_historical_type sumcheckFoldOracleReduction_perfectCompleteness
  sumcheckFoldOracleReduction_perfectCompleteness_historicalType

theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness_historicalType :
    OracleVerifier.rbrKnowledgeSoundnessAveraged (oSpec := []ₒ) (StmtIn :=
      Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
      (OStmtIn :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (WitIn := RingSwitching.SumcheckWitness L ℓ' 0) (StmtOut :=
      Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
        (Fin.last ℓ'))
      (OStmtOut :=
      BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        (Fin.last ℓ'))
      (WitOut :=
      BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
        (Fin.last ℓ'))
      (pSpec :=
      BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn :=
      RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
        (aOStmtIn :=
        BinaryBasefoldAbstractOStmtIn (κ := κ) (L := L) (K := K) (β := β) (ℓ' :=
          ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        0)
      (relOut :=
      BinaryBasefold.roundRelation (mp :=
        RingSwitching_BBFSumcheckMultParam κ L K (β :=
          booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)
        (Fin.last ℓ'))
      (verifier :=
      sumcheckFoldOracleVerifier κ L K β ℓ ℓ' (h_l := h_l) 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init) (impl := impl) (rbrKnowledgeError :=
      BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError K β (ϑ := ϑ)) :=
  by historical_exact sumcheckFoldOracleVerifier_rbrKnowledgeSoundness

assert_historical_type sumcheckFoldOracleVerifier_rbrKnowledgeSoundness
  sumcheckFoldOracleVerifier_rbrKnowledgeSoundness_historicalType

end Security

end SumcheckFold

end

end Binius.FRIBinius.CoreInteractionPhase
