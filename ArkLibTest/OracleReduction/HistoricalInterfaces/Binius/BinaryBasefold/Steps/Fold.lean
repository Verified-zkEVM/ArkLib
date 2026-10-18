/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold
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

open Binius.BinaryBasefold

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


section FoldStep

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {n : ℕ}
  {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

open scoped NNReal

open Classical in
omit [DecidableEq 𝔽q] in
theorem foldOracleVerifier_rbrKnowledgeSoundness_historicalType (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp :=
          mp) i).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc)
      (relOut :=
      foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  by historical_exact foldOracleVerifier_rbrKnowledgeSoundness

assert_historical_type foldOracleVerifier_rbrKnowledgeSoundness
  foldOracleVerifier_rbrKnowledgeSoundness_historicalType

end FoldStep

end SingleIteratedSteps

end

end Binius.BinaryBasefold.CoreInteraction
