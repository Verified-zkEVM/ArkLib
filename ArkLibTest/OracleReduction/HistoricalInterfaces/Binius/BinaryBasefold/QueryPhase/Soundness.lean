/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Soundness
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

open OracleSpec

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section

open OracleSpec _root_.OracleComp

open AdditiveNTT Polynomial MvPolynomial ProtocolSpec

open Probability

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

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

open scoped NNReal

omit [CharP L 2] [SampleableType L] in
theorem queryOracleVerifier_rbrKnowledgeSoundness_historicalType {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ := ϑ)
          γ_repetitions).rbrKnowledgeSoundnessAveraged
      init impl (Oₛₒ := fun i : Empty => nomatch i) (relIn :=
      finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relOut := acceptRejectOracleRel) (rbrKnowledgeError :=
      queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact queryOracleVerifier_rbrKnowledgeSoundness

assert_historical_type queryOracleVerifier_rbrKnowledgeSoundness
  queryOracleVerifier_rbrKnowledgeSoundness_historicalType

end FinalQueryRoundIOR

end

end Binius.BinaryBasefold.QueryPhase
