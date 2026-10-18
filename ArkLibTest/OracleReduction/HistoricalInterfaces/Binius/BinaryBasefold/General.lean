/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.General
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

open AdditiveNTT Polynomial

namespace Binius.BinaryBasefold.FullBinaryBasefold

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset
  AdditiveNTT

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


variable [hdiv : Fact (ϑ ∣ ℓ)]

variable {𝓑 : Fin 2 ↪ L}

open CoreInteraction QueryPhase

attribute [local instance] CoreInteraction.foldChallengeFintypes
  CoreInteraction.foldChallengeInhabited CoreInteraction.commitChallengeFintypes
  CoreInteraction.commitChallengeInhabited

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [CharP L 2] in
theorem fullOracleReduction_perfectCompleteness_historicalType :
    OracleProof.perfectCompleteness (oracleProof :=
      fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (relation :=
      strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (init := init) (impl := impl) :=
  by historical_exact fullOracleReduction_perfectCompleteness

assert_historical_type fullOracleReduction_perfectCompleteness
  fullOracleReduction_perfectCompleteness_historicalType

open scoped NNReal

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem fullOracleVerifier_rbrKnowledgeSoundness_historicalType :
    OracleProof.rbrKnowledgeSoundnessAveraged init impl (verifier :=
      fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (relIn :=
      roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (rbrKnowledgeError :=
      fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact fullOracleVerifier_rbrKnowledgeSoundness

assert_historical_type fullOracleVerifier_rbrKnowledgeSoundness
  fullOracleVerifier_rbrKnowledgeSoundness_historicalType

theorem fullOracleVerifier_knowledgeSoundness_historicalType :
    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
          (fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ) (𝓑 := 𝓑)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate))).knowledgeSoundness
      init impl (relIn :=
      roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := acceptRejectOracleRel) (knowledgeError :=
      concreteBinaryBasefoldKnowledgeError L ℓ 𝓡 γ_repetitions) :=
  by historical_exact fullOracleVerifier_knowledgeSoundness

assert_historical_type fullOracleVerifier_knowledgeSoundness
  fullOracleVerifier_knowledgeSoundness_historicalType

end Binius.BinaryBasefold.FullBinaryBasefold
