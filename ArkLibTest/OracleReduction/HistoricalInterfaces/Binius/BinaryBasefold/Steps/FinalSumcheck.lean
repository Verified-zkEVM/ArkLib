/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction

noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial

open scoped NNReal ProbabilityTheory

variable {r : ℕ} [NeZero r]

variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]

variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]

variable [Algebra 𝔽q L]

variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]

variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡]
  [NeZero ϑ] -- Should we allow ℓ = 0?


variable
  {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}


variable {𝓑 : Fin 2 ↪ L}

variable [hdiv : Fact (ϑ ∣ ℓ)]

section SingleIteratedSteps

variable {Context : Type}
  {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context


section FinalSumcheckStep

omit [DecidableEq 𝔽q] in
omit [CharP L 2] in
theorem finalSumcheckOracleReduction_perfectCompleteness_historicalType
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness (pSpec :=
      pSpecFinalSumcheckStep (L := L)) (relIn :=
      strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 :=
        𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
      (relOut :=
      strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (oracleReduction :=
      finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (init := init) (impl := impl) :=
  by historical_exact finalSumcheckOracleReduction_perfectCompleteness

assert_historical_type finalSumcheckOracleReduction_perfectCompleteness
  finalSumcheckOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] [CharP L 2] in
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 :=
          𝓑)).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam)
        (Fin.last ℓ))
      (relOut :=
      finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError) :=
  by historical_exact finalSumcheckOracleVerifier_rbrKnowledgeSoundness

assert_historical_type finalSumcheckOracleVerifier_rbrKnowledgeSoundness
  finalSumcheckOracleVerifier_rbrKnowledgeSoundness_historicalType

end FinalSumcheckStep

end SingleIteratedSteps

end

end Binius.BinaryBasefold.CoreInteraction
