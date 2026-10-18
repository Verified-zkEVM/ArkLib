/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Protocol
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

section ComponentReductions

variable {Context : Type}
  {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context


section FoldRelayRound

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
theorem foldRelayOracleReduction_perfectCompleteness_historicalType (i : Fin ℓ)
    (hNCR : ¬isCommitmentRound ℓ ϑ i)
    [(i : pSpecFold.ChallengeIdx) →
        Inhabited ((pSpecFold (L := L)).Challenge i)] :
    OracleReduction.perfectCompleteness (pSpec := pSpecFoldRelay (L := L))
      (relIn :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
      (relOut :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (oracleReduction :=
      foldRelayOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) i hNCR)
      (init := init) (impl := impl) :=
  by historical_exact foldRelayOracleReduction_perfectCompleteness

assert_historical_type foldRelayOracleReduction_perfectCompleteness
  foldRelayOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] in
theorem foldRelayOracleVerifier_rbrKnowledgeSoundness_historicalType (i : Fin ℓ)
    (hNCR : ¬isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) i hNCR).rbrKnowledgeSoundnessAveraged
      (init := init) (impl := impl) (relIn :=
      roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        i.castSucc (mp := mp))
      (relOut :=
      roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        i.succ (mp := mp))
      (rbrKnowledgeError :=
      foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i) :=
  by historical_exact foldRelayOracleVerifier_rbrKnowledgeSoundness

assert_historical_type foldRelayOracleVerifier_rbrKnowledgeSoundness
  foldRelayOracleVerifier_rbrKnowledgeSoundness_historicalType

end FoldRelayRound

section FoldCommitRound

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
theorem foldCommitOracleReduction_perfectCompleteness_historicalType (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i)
    [(i : pSpecFold.ChallengeIdx) →
        Inhabited ((pSpecFold (L := L)).Challenge i)]
    [(j :
          (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              i).ChallengeIdx) →
        Inhabited
          ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge
            j)] :
    OracleReduction.perfectCompleteness (pSpec :=
      pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) (relIn :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
      (relOut :=
      strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (oracleReduction :=
      foldCommitOracleReduction 𝔽q β (ϑ := ϑ) (mp := mp) (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR)
      (init := init) (impl := impl) :=
  by historical_exact foldCommitOracleReduction_perfectCompleteness

assert_historical_type foldCommitOracleReduction_perfectCompleteness
  foldCommitOracleReduction_perfectCompleteness_historicalType

omit [DecidableEq 𝔽q] in
theorem foldCommitOracleVerifier_rbrKnowledgeSoundness_historicalType
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) i hCR).rbrKnowledgeSoundnessAveraged
      (init := init) (impl := impl) (relIn :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc)
      (relOut :=
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (rbrKnowledgeError :=
      foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i) :=
  by historical_exact foldCommitOracleVerifier_rbrKnowledgeSoundness

assert_historical_type foldCommitOracleVerifier_rbrKnowledgeSoundness
  foldCommitOracleVerifier_rbrKnowledgeSoundness_historicalType

end FoldCommitRound

section IteratedSumcheckFoldComposition

section composedOracleVerifiers

end composedOracleVerifiers

section composedOracleRedutions

end composedOracleRedutions

end IteratedSumcheckFoldComposition

end ComponentReductions

end

end Binius.BinaryBasefold.CoreInteraction
