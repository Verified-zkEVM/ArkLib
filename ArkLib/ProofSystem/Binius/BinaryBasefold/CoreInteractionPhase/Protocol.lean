/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps
public import ArkLib.OracleReduction.CastIdx
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness

/-!
# Binary Basefold: the rounds and blocks of the core interaction

The sum-check-and-fold rounds of the Binary Basefold core interaction, assembled from the single
steps of `Steps`. Round `i` is the fold step, followed by the commit step if `i` is a commitment
round (`ϑ ∣ i + 1` and `i + 1 < ℓ`) and by the relay step otherwise. The `ℓ` rounds fall into
`ℓ / ϑ` blocks of `ϑ` rounds: a non-last block is `ϑ - 1` fold-relay rounds and a closing
fold-commit round, and the last block is `ϑ` fold-relay rounds.

## Main definitions and statements

* `foldRelayOracleVerifier`, `foldCommitOracleVerifier` and their reductions: one round. Their
  worst-case round-by-round knowledge soundness (`…_rbrKnowledgeSoundnessWorstCase`) comes from
  the steps' theorems by `OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`,
  guarded by the fold step's check; the averaged forms and perfect completeness are included. The
  error is the fold step's on its challenge, `foldRelayKnowledgeError` and
  `foldCommitKnowledgeError`.
* `nonLastSingleBlockOracleVerifier`, `nonLastBlocksOracleVerifier`, `lastBlockOracleVerifier`,
  `sumcheckFoldOracleVerifier` and their reductions: the blocks and the whole sequence of rounds,
  by `OracleVerifier.append` and `OracleVerifier.seqCompose`. Where the composition reaches a round
  under an index that is equal but not definitionally equal to the expected one (the round after
  a block's commitment round, `(ℓ / ϑ - 1) · ϑ + ϑ` for `ℓ`, `0 · ϑ` for `0`), the composite is
  moved along the equality by `OracleVerifier.castIdx`.
* The guarded forms `…GuardedForm` of the rounds and composites: the checks of their steps in
  order, built from the steps' own guarded forms by `OracleVerifier.appendGuardedForm`,
  `OracleVerifier.seqComposeGuardedForm` and `OracleVerifier.castIdxGuardedForm`.

The security of the blocks is in `CoreInteractionPhase/Security.lean`, and the core interaction
with its final sum-check step is in `CoreInteractionPhase.lean`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The rounds are lines 1–6 of the loop of the evaluation IOP of Construction 4.12, without the
  final constant of line 5.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section ComponentReductions
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

section FoldRelayRound

/-- The `i`-th round outside a commitment round: the fold step, then the relay step. -/
@[reducible]
def foldRelayOracleVerifier (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleVerifier []ₒ
      (Statement (L := L) Context i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Statement (L := L) Context i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecFoldRelay (L := L)) :=
  OracleVerifier.append
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)

/-- The oracle reduction of the `i`-th round outside a commitment round. -/
@[reducible]
def foldRelayOracleReduction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleReduction []ₒ
      (Statement (L := L) Context i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
      (Statement (L := L) Context i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
      (pSpecFoldRelay (L := L)) :=
  OracleReduction.append
    (foldOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)

/-- The guarded form of the fold-relay round: the fold step's check, then the relay step's
trivially-true one. -/
def foldRelayOracleVerifierGuardedForm (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i hNCR).toVerifier.GuardedForm :=
  OracleVerifier.appendGuardedForm
    (foldOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (relayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- Perfect completeness of the fold-relay round, from the strict round relation at `i` to the
strict round relation at `i + 1`. -/
theorem foldRelayOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFoldRelay (L := L))
      (relIn := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (oracleReduction := foldRelayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly) i hNCR)
      (init := init) (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (foldOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (relayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)
    (fun _ => Or.inl inferInstance)
    (foldOracleReduction_perfectCompleteness 𝔽q β i)
    (fun _ => relayOracleReduction_perfectCompleteness 𝔽q β i hNCR)

/-- The round-by-round knowledge error of the fold-relay round: the fold step's error on its
challenge. The relay step has none. -/
def foldRelayKnowledgeError (i : Fin ℓ) : (pSpecFoldRelay (L := L)).ChallengeIdx → ℝ≥0 :=
  Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    relayKnowledgeError ∘ ChallengeIdx.sumEquiv.symm

omit [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the fold-relay round, from the round
relation at `i` to the round relation at `i + 1`, with error `foldRelayKnowledgeError`. -/
theorem foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i hNCR).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (foldOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (foldOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β i)
    (relayOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β i hNCR)

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the fold-relay round: the averaged form of
`foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem foldRelayOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i hNCR).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (rbrKnowledgeError := foldRelayKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β i hNCR)

end FoldRelayRound

section FoldCommitRound

/-- The `i`-th round at a commitment round: the fold step, then the commit step. -/
@[reducible]
def foldCommitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    OracleVerifier []ₒ
      (Statement (L := L) Context i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Statement (L := L) Context i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleVerifier.append
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

/-- The oracle reduction of the `i`-th round at a commitment round. -/
@[reducible]
def foldCommitOracleReduction (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    OracleReduction []ₒ
      (Statement (L := L) Context i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
      (Statement (L := L) Context i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
      (pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleReduction.append
    (foldOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (commitOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

/-- The guarded form of the fold-commit round: the fold step's check, then the commit step's
trivially-true one. -/
def foldCommitOracleVerifierGuardedForm (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i hCR).toVerifier.GuardedForm :=
  OracleVerifier.appendGuardedForm
    (foldOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (commitOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- Perfect completeness of the fold-commit round, from the strict round relation at `i` to the
strict round relation at `i + 1`. -/
theorem foldCommitOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (oracleReduction := foldCommitOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly) i hCR)
      (init := init) (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (foldOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (commitOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
    (fun _ => Or.inl inferInstance)
    (foldOracleReduction_perfectCompleteness 𝔽q β i)
    (fun _ => commitOracleReduction_perfectCompleteness 𝔽q β i hCR)

/-- The round-by-round knowledge error of the fold-commit round: the fold step's error on its
challenge. The commit step has none. -/
def foldCommitKnowledgeError (i : Fin ℓ) :
    (pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx → ℝ≥0 :=
  Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ∘ ChallengeIdx.sumEquiv.symm

omit [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the fold-commit round, from the round
relation at `i` to the round relation at `i + 1`, with error `foldCommitKnowledgeError`. -/
theorem foldCommitOracleVerifier_rbrKnowledgeSoundnessWorstCase (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i hCR).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (foldOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
    (foldOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β i)
    (commitOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β i hCR)

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the fold-commit round: the averaged form of
`foldCommitOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem foldCommitOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i hCR).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (rbrKnowledgeError := foldCommitKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (foldCommitOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β i hCR)

end FoldCommitRound

section IteratedSumcheckFoldComposition

/-! ### Round indices of the blocks -/

/-- The commitment round of the `bIdx`-th non-last block: its last round. -/
def nonLastSingleBlockCommitIdx (bIdx : Fin (ℓ / ϑ - 1)) : Fin ℓ :=
  ⟨bIdx * ϑ + (ϑ - 1), bIdx_mul_ϑ_add_i_lt_ℓ_succ (m := 0) bIdx
    ⟨ϑ - 1, Nat.sub_one_lt (NeZero.ne ϑ)⟩⟩

/-- The round after the commitment round of the `bIdx`-th non-last block is the first round of
the next block. -/
lemma nonLastSingleBlockCommitIdx_succ (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx).succ =
      ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩ := by
  refine Fin.ext ?_
  simp only [nonLastSingleBlockCommitIdx, Fin.val_succ]
  rw [Nat.add_assoc, Nat.sub_add_cancel (NeZero.one_le), Nat.add_mul, Nat.one_mul]

/-- The first round of the last block, written as the start of a sequence of rounds. -/
lemma lastBlockStartIdx_eq :
    (⟨(ℓ / ϑ - 1) * ϑ + ↑(0 : Fin (ϑ + 1)),
      lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (ℓ := ℓ) _ (hx := Fin.is_le _)⟩ : Fin (ℓ + 1)) =
      ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (ℓ := ℓ) 0 (hx := Nat.zero_le _)⟩ :=
  Fin.ext (by simp)

/-- The last block ends at the last round. -/
lemma lastBlockEndIdx_eq :
    (⟨(ℓ / ϑ - 1) * ϑ + ↑(Fin.last ϑ),
      lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (ℓ := ℓ) _ (hx := Fin.is_le _)⟩ : Fin (ℓ + 1)) =
      Fin.last ℓ := by
  have hpos : 0 < ℓ / ϑ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out)
    (Nat.pos_of_neZero ϑ)
  refine Fin.ext ?_
  simp only [Fin.val_last]
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos, Nat.div_mul_cancel hdiv.out]

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- The first block starts at round `0`. -/
lemma fin_zero_mul_eq (h : 0 * ϑ < ℓ + 1) : (⟨0 * ϑ, h⟩ : Fin (ℓ + 1)) = 0 :=
  Fin.ext (Nat.zero_mul ϑ)

/-! ### The composed oracle verifiers -/

/-- The `bIdx`-th non-last block: `ϑ - 1` fold-relay rounds, then a fold-commit round. -/
def nonLastSingleBlockOracleVerifier (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleVerifier []ₒ
      (Statement (L := L) (ℓ := ℓ) Context
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (Statement (L := L) (ℓ := ℓ) Context ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) :=
  OracleVerifier.append
    (OracleVerifier.seqCompose
      (fun i : Fin (ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (fun i : Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun i => foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt))))
    (OracleVerifier.castIdx (StmtIn := fun i => Statement (L := L) (ℓ := ℓ) Context i)
      (OStmtIn := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (StmtOut := fun i => Statement (L := L) (ℓ := ℓ) Context i)
      (OStmtOut := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      rfl (nonLastSingleBlockCommitIdx_succ bIdx)
      (foldCommitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) (nonLastSingleBlockCommitIdx bIdx)
        (isCommitmentRoundOfNonLastBlock (r := r) (𝓡 := 𝓡) bIdx)))

/-- The non-last blocks in sequence, from round `0` to the first round of the last block. -/
def nonLastBlocksOracleVerifier :
    OracleVerifier []ₒ
      (Statement (L := L) (ℓ := ℓ) Context ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (Statement (L := L) (ℓ := ℓ) Context
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.seqCompose
    (fun i : Fin (ℓ / ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (fun i : Fin (ℓ / ϑ - 1 + 1) => OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (pSpec := fun bIdx => pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (fun bIdx => nonLastSingleBlockOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multpoly) bIdx)

/-- The last block: `ϑ` fold-relay rounds, from round `(ℓ / ϑ - 1) · ϑ` to round `ℓ`. -/
def lastBlockOracleVerifier :
    OracleVerifier []ₒ
      (Statement (L := L) (ℓ := ℓ) Context
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (pSpecLastBlock (L := L) (ϑ := ϑ)) :=
  OracleVerifier.castIdx (StmtIn := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtIn := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (StmtOut := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtOut := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    lastBlockStartIdx_eq lastBlockEndIdx_eq
    (OracleVerifier.seqCompose
      (fun i : Fin (ϑ + 1) => Statement (L := L) (ℓ := ℓ) Context
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩)
      (fun i : Fin (ϑ + 1) => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun i => foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i)))

/-- The sum-check-and-fold rounds of the core interaction: the non-last blocks, then the last
block, from round `0` to round `ℓ`. -/
def sumcheckFoldOracleVerifier :
    OracleVerifier []ₒ
      (Statement (L := L) (ℓ := ℓ) Context 0)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.castIdx (StmtIn := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtIn := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (StmtOut := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtOut := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (fin_zero_mul_eq (ϑ := ϑ) _) rfl
    (OracleVerifier.append
      (nonLastBlocksOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly))
      (lastBlockOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly)))

/-! ### The composed oracle reductions -/

/-- The oracle reduction of the `bIdx`-th non-last block. -/
def nonLastSingleBlockOracleReduction (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction []ₒ
      (Statement (L := L) (ℓ := ℓ) Context
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (Statement (L := L) (ℓ := ℓ) Context ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) :=
  OracleReduction.append
    (OracleReduction.seqCompose
      (fun i : Fin (ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (fun i : Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (fun i : Fin (ϑ - 1 + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ℓ := ℓ) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun i => foldRelayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt))))
    (OracleReduction.castIdx (StmtIn := fun i => Statement (L := L) (ℓ := ℓ) Context i)
      (OStmtIn := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (WitIn := fun i => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
      (StmtOut := fun i => Statement (L := L) (ℓ := ℓ) Context i)
      (OStmtOut := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (WitOut := fun i => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
      rfl (nonLastSingleBlockCommitIdx_succ bIdx)
      (foldCommitOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) (nonLastSingleBlockCommitIdx bIdx)
        (isCommitmentRoundOfNonLastBlock (r := r) (𝓡 := 𝓡) bIdx)))

/-- The oracle reduction of the non-last blocks in sequence. -/
def nonLastBlocksOracleReduction :
    OracleReduction []ₒ
      (Statement (L := L) (ℓ := ℓ) Context ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (Statement (L := L) (ℓ := ℓ) Context
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.seqCompose
    (fun i : Fin (ℓ / ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (fun i : Fin (ℓ / ϑ - 1 + 1) => OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (fun i : Fin (ℓ / ϑ - 1 + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (pSpec := fun bIdx => pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (fun bIdx => nonLastSingleBlockOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multpoly) bIdx)

/-- The oracle reduction of the last block. -/
def lastBlockOracleReduction :
    OracleReduction []ₒ
      (Statement (L := L) (ℓ := ℓ) Context
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (Fin.last ℓ))
      (pSpecLastBlock (L := L) (ϑ := ϑ)) :=
  OracleReduction.castIdx (StmtIn := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtIn := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitIn := fun i => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
    (StmtOut := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtOut := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitOut := fun i => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
    lastBlockStartIdx_eq lastBlockEndIdx_eq
    (OracleReduction.seqCompose
      (fun i : Fin (ϑ + 1) => Statement (L := L) (ℓ := ℓ) Context
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩)
      (fun i : Fin (ϑ + 1) => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩)
      (fun i : Fin (ϑ + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun i => foldRelayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i)))

/-- The oracle reduction of the sum-check-and-fold rounds. -/
def sumcheckFoldOracleReduction :
    OracleReduction []ₒ
      (Statement (L := L) (ℓ := ℓ) Context 0)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
      (Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (Fin.last ℓ))
      (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.castIdx (StmtIn := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtIn := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitIn := fun i => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
    (StmtOut := fun i => Statement (L := L) (ℓ := ℓ) Context i)
    (OStmtOut := fun i => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitOut := fun i => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
    (fin_zero_mul_eq (ϑ := ϑ) _) rfl
    (OracleReduction.append
      (nonLastBlocksOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly))
      (lastBlockOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly)))

/-! ### Guarded forms of the composed verifiers -/

/-- The guarded form of the fold-relay rounds of the `bIdx`-th non-last block: their checks in
sequence. -/
def nonLastSingleBlockFoldRelayGuardedForm (bIdx : Fin (ℓ / ϑ - 1)) :
    (OracleVerifier.seqCompose
      (fun i : Fin (ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (fun i : Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun i => foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt)))).toVerifier.GuardedForm :=
  OracleVerifier.seqComposeGuardedForm
    (fun i : Fin (ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
      ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
    (fun i : Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
    (pSpec := fun _ => pSpecFoldRelay (L := L))
    (fun i => foldRelayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
      (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt)))

/-- The guarded form of the `bIdx`-th non-last block: the checks of its fold-relay rounds, then
those of its fold-commit round. -/
def nonLastSingleBlockOracleVerifierGuardedForm (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) bIdx).toVerifier.GuardedForm :=
  OracleVerifier.appendGuardedForm
    (nonLastSingleBlockFoldRelayGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) bIdx)
    (OracleVerifier.castIdxGuardedForm rfl (nonLastSingleBlockCommitIdx_succ bIdx)
      (foldCommitOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) (nonLastSingleBlockCommitIdx bIdx)
        (isCommitmentRoundOfNonLastBlock (r := r) (𝓡 := 𝓡) bIdx)))

/-- The guarded form of the non-last blocks: the blocks' checks in sequence. -/
def nonLastBlocksOracleVerifierGuardedForm :
    (nonLastBlocksOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).toVerifier.GuardedForm :=
  OracleVerifier.seqComposeGuardedForm _ _
    (fun bIdx => nonLastSingleBlockOracleVerifierGuardedForm 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) bIdx)

/-- The guarded form of the last block: its fold-relay rounds' checks in sequence. -/
def lastBlockOracleVerifierGuardedForm :
    (lastBlockOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).toVerifier.GuardedForm :=
  OracleVerifier.castIdxGuardedForm lastBlockStartIdx_eq lastBlockEndIdx_eq
    (OracleVerifier.seqComposeGuardedForm _ _ (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun i => foldRelayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i)))

/-- The guarded form of the sum-check-and-fold rounds: the non-last blocks' checks, then the last
block's. -/
def sumcheckFoldOracleVerifierGuardedForm :
    (sumcheckFoldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).toVerifier.GuardedForm :=
  OracleVerifier.castIdxGuardedForm (fin_zero_mul_eq (ϑ := ϑ) _) rfl
    (OracleVerifier.appendGuardedForm
      (nonLastBlocksOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly))
      (lastBlockOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly)))

end IteratedSumcheckFoldComposition

end ComponentReductions

end
end Binius.BinaryBasefold.CoreInteraction
