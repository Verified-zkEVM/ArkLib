/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section
  /- The composed verifier/reduction bundles below are `def`s whose *inferred* type embeds the
  inline `Fin` bounds proofs written in their bodies. Under the module system's default, such a
  proof is abstracted into a private auxiliary theorem, which a public signature may not mention;
  exposing the bodies instead delays every `by` until the (still unknown) result type is solved.
  `backward.proofsInPublic` restores the classic elaboration these definitions were written
  against. See docs/wiki/module-system.md. -/


namespace Binius.BinaryBasefold.CoreInteraction

noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial Equiv

open scoped NNReal

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

section CoreInteractionPhaseReduction

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] [CharP L 2] in
theorem coreInteractionOracleReduction_perfectCompleteness_historicalType
    [(j : pSpecFold.ChallengeIdx) →
        Inhabited ((pSpecFold (L := L)).Challenge j)]
    [(j : pSpecFold.ChallengeIdx) →
        SampleableType ((pSpecFold (L := L)).Challenge j)]
    [(i : Fin ℓ) →
        (j :
            (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                i).ChallengeIdx) →
          Inhabited
            ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge
              j)]
    [(i : Fin ℓ) →
        (j :
            (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                i).ChallengeIdx) →
          SampleableType
            ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge
              j)] :
    OracleReduction.perfectCompleteness (pSpec :=
      pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (relIn :=
      strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut :=
      strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑))
      (init := init) (impl := impl) :=
  by historical_exact coreInteractionOracleReduction_perfectCompleteness

assert_historical_type coreInteractionOracleReduction_perfectCompleteness
  coreInteractionOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] in
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness_historicalType :
    (coreInteractionOracleVerifier 𝔽q β (𝓑 := 𝓑)).rbrKnowledgeSoundnessAveraged
      init impl (pSpec :=
      pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (relIn :=
      roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut :=
      finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError :=
      coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)) :=
  by historical_exact coreInteractionOracleVerifier_rbrKnowledgeSoundness

assert_historical_type coreInteractionOracleVerifier_rbrKnowledgeSoundness
  coreInteractionOracleVerifier_rbrKnowledgeSoundness_historicalType

end CoreInteractionPhaseReduction

end

end Binius.BinaryBasefold.CoreInteraction
