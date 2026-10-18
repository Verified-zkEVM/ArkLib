/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Security
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

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

section ComponentReductions

variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

section IteratedSumcheckFoldComposition

section SecurityProps

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
theorem nonLastSingleBlockOracleReduction_perfectCompleteness_historicalType
    (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl) (relIn :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨bIdx * ϑ, by
          apply
            Nat.lt_trans (m := ℓ) (h₁ := by
              change
                bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val <
                  ℓ + 0
              apply bIdx_mul_ϑ_add_i_lt_ℓ_succ) (by omega)⟩)
      (relOut :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (oracleReduction :=
      nonLastSingleBlockOracleReduction 𝔽q β (ϑ := ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) bIdx) :=
  by historical_exact nonLastSingleBlockOracleReduction_perfectCompleteness

assert_historical_type nonLastSingleBlockOracleReduction_perfectCompleteness
  nonLastSingleBlockOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
theorem lastBlockOracleReduction_perfectCompleteness_historicalType :
    OracleReduction.perfectCompleteness (init := init) (impl := impl) (relIn :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
      (relOut :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ))
      (oracleReduction :=
      lastBlockOracleReduction 𝔽q β (ϑ := ϑ) (mp := mp) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑)) :=
  by historical_exact lastBlockOracleReduction_perfectCompleteness

assert_historical_type lastBlockOracleReduction_perfectCompleteness
  lastBlockOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
theorem sumcheckFoldOracleReduction_perfectCompleteness_historicalType :
    OracleReduction.perfectCompleteness (pSpec :=
      pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (relIn :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ))
      (oracleReduction :=
      sumcheckFoldOracleReduction 𝔽q β (ϑ := ϑ) (mp := mp) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (init := init) (impl := impl) :=
  by historical_exact sumcheckFoldOracleReduction_perfectCompleteness

assert_historical_type sumcheckFoldOracleReduction_perfectCompleteness
  sumcheckFoldOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] in
theorem lastBlockOracleVerifier_rbrKnowledgeSoundness_historicalType :
    OracleVerifier.rbrKnowledgeSoundnessAveraged init impl
      (roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
      (roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (Fin.last ℓ))
      (lastBlockOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (rbrKnowledgeError :=
      lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact lastBlockOracleVerifier_rbrKnowledgeSoundness

assert_historical_type lastBlockOracleVerifier_rbrKnowledgeSoundness
  lastBlockOracleVerifier_rbrKnowledgeSoundness_historicalType

omit [DecidableEq 𝔽q] in
theorem nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness_historicalType
    (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          bIdx).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)
        ⟨bIdx * ϑ, by
          apply
            Nat.lt_trans (m := ℓ) (h₁ := by
              change
                bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val <
                  ℓ + 0
              apply bIdx_mul_ϑ_add_i_lt_ℓ_succ) (by omega)⟩)
      (relOut :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (rbrKnowledgeError :=
      nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) :=
  by historical_exact nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness

assert_historical_type nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness
  nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness_historicalType

omit [DecidableEq 𝔽q] in
theorem nonLastBlocksOracleVerifier_rbrKnowledgeSoundness_historicalType :
    (nonLastBlocksOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate) (𝓑 := 𝓑)).rbrKnowledgeSoundnessAveraged
      init impl (relIn :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) ⟨0 * ϑ, by omega⟩)
      (relOut :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
      (rbrKnowledgeError :=
      nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact nonLastBlocksOracleVerifier_rbrKnowledgeSoundness

assert_historical_type nonLastBlocksOracleVerifier_rbrKnowledgeSoundness
  nonLastBlocksOracleVerifier_rbrKnowledgeSoundness_historicalType

omit [DecidableEq 𝔽q] in
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness_historicalType :
    (sumcheckFoldOracleVerifier 𝔽q β (mp := mp) (𝓑 :=
          𝓑)).rbrKnowledgeSoundnessAveraged
      init impl (pSpec :=
      pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) 0)
      (relOut :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (Fin.last ℓ))
      (rbrKnowledgeError :=
      sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)) :=
  by historical_exact sumcheckFoldOracleVerifier_rbrKnowledgeSoundness

assert_historical_type sumcheckFoldOracleVerifier_rbrKnowledgeSoundness
  sumcheckFoldOracleVerifier_rbrKnowledgeSoundness_historicalType

end SecurityProps

end IteratedSumcheckFoldComposition

end ComponentReductions

end

end Binius.BinaryBasefold.CoreInteraction
