/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.BBFSmallFieldIOPCS
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

namespace Binius.RingSwitching.BBFSmallFieldIOPCS

open Binius.BinaryBasefold hiding MLPEvalStatement

open Binius.BinaryBasefold.FullBinaryBasefold

open _root_.RingSwitching _root_.RingSwitching.FullRingSwitching
  _root_.RingSwitching.BatchingPhase

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset
  AdditiveNTT Module

open scoped NNReal

noncomputable section

section BinaryBasefoldMLIOPCS

variable {r : ℕ} [NeZero r]

variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]

variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]

variable [Algebra 𝔽q L]

variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]

variable {ℓ' 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]

variable {h_ℓ_add_R_rate : ℓ' + 𝓡 < r}

variable {𝓑 : Fin 2 ↪ L}

variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]

variable [hdiv : Fact (ϑ ∣ ℓ')]

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [CharP L 2] in
theorem largeFieldInvocationOracleReduction_perfectCompleteness_historicalType :
    OracleReduction.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i)
      (oracleReduction :=
      largeFieldInvocationOracleReduction 𝔽q β γ_repetitions (𝓑 := 𝓑)) (relIn :=
      (bbfAbstractOStmtIn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ :=
          ϑ)).toStrictRelInput)
      (relOut := acceptRejectOracleRel) (init := init) (impl := impl) :=
  by historical_exact largeFieldInvocationOracleReduction_perfectCompleteness

assert_historical_type largeFieldInvocationOracleReduction_perfectCompleteness
  largeFieldInvocationOracleReduction_perfectCompleteness_historicalType

end BinaryBasefoldMLIOPCS

section Composition

variable {r : ℕ} [NeZero r]

variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]

variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]

variable [Algebra 𝔽q L]

variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]

variable {ℓ' 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]

variable {h_ℓ_add_R_rate : ℓ' + 𝓡 < r}

variable {𝓑 : Fin 2 ↪ L}

variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]

variable
  [hdiv : Fact (ϑ ∣ ℓ')]
    -- Ring-switching variables


variable (κ : ℕ) [NeZero κ]

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

variable [Algebra K L]

variable (β_rs : Basis (Fin κ → Fin 2) K L)

variable (ℓ : ℕ) [NeZero ℓ]

variable (h_l : ℓ = ℓ' + κ)

variable {σ : Type} (init : ProbComp σ)
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq K] [Fintype K] in
theorem bbf_fullOracleReduction_perfectCompleteness_historicalType :
    OracleReduction.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i)
      (oracleReduction :=
      FullRingSwitching.fullOracleReduction κ L K (bbfProfile κ K β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (relIn :=
      BatchingPhase.strictBatchingInputRelation κ L K (bbfProfile κ K β_rs) ℓ ℓ'
        h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
            h_ℓ_add_R_rate) (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel) (init := init) (impl := impl) :=
  by historical_exact bbf_fullOracleReduction_perfectCompleteness

assert_historical_type bbf_fullOracleReduction_perfectCompleteness
  bbf_fullOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq K] [Fintype K] in
theorem bbf_fullOracleVerifier_rbrKnowledgeSoundness_historicalType :
    OracleVerifier.rbrKnowledgeSoundnessAveraged (Oₛₒ := fun i : Empty =>
      nomatch i) (verifier :=
      FullRingSwitching.fullOracleVerifier κ L K (bbfProfile κ K β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (init := init) (impl := impl) (relIn :=
      BatchingPhase.batchingInputRelation κ L K (bbfProfile κ K β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
            h_ℓ_add_R_rate) (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel) (rbrKnowledgeError := fun i =>
      FullRingSwitching.fullRbrKnowledgeError κ L K (bbfProfile κ K β_rs) ℓ'
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate) (𝓑 := 𝓑))
        i) :=
  by historical_exact bbf_fullOracleVerifier_rbrKnowledgeSoundness

assert_historical_type bbf_fullOracleVerifier_rbrKnowledgeSoundness
  bbf_fullOracleVerifier_rbrKnowledgeSoundness_historicalType

omit [DecidableEq K] [Fintype K] in
theorem bbf_fullOracleVerifier_knowledgeSoundness_historicalType :
    (FullRingSwitching.fullOracleVerifier κ L K (bbfProfile κ K β_rs) ℓ ℓ' h_l
              (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
                h_ℓ_add_R_rate) (𝓑 := 𝓑))).toVerifier
          (Oₛₒ := fun i : Empty => nomatch i).knowledgeSoundness
      (init := init) (impl := impl) (relIn :=
      BatchingPhase.batchingInputRelation κ L K (bbfProfile κ K β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
            h_ℓ_add_R_rate) (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel) (knowledgeError :=
      bbfSmallFieldConcreteKnowledgeError κ K β_rs
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate) (𝓑 := 𝓑))) :=
  by historical_exact bbf_fullOracleVerifier_knowledgeSoundness

assert_historical_type bbf_fullOracleVerifier_knowledgeSoundness
  bbf_fullOracleVerifier_knowledgeSoundness_historicalType

end Composition

end

end Binius.RingSwitching.BBFSmallFieldIOPCS
