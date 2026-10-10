/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Protocol
public import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound

/-!
# Binary Basefold: security of the blocks of the core interaction

Perfect completeness and round-by-round knowledge soundness of the blocks of sum-check-and-fold
rounds defined in `CoreInteractionPhase/Protocol.lean`, and of their sequence.

## Main statements

* `nonLastSingleBlockOracleReduction_perfectCompleteness`,
  `lastBlockOracleReduction_perfectCompleteness`,
  `nonLastBlocksOracleReduction_perfectCompleteness`,
  `sumcheckFoldOracleReduction_perfectCompleteness`: perfect completeness between the strict round
  relations at the ends, from the rounds' theorems by
  `OracleReduction.append_perfectCompleteness_of_guarded_verifiers`,
  `OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers` and
  `OracleReduction.castIdx_perfectCompleteness`.
* `nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase`,
  `lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase`,
  `nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase`,
  `sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase`: worst-case round-by-round knowledge
  soundness between the round relations at the ends, from the rounds' theorems by
  `OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`,
  `OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded` and
  `OracleVerifier.castIdx_rbrKnowledgeSoundnessWorstCase`. Each composite is guarded by the
  checks of its own steps. Each challenge's error is that of the fold step it belongs to; the
  errors are `lastBlockRbrKnowledgeError`, `nonLastSingleBlockRbrKnowledgeError`,
  `nonLastBlocksRbrKnowledgeError` and `sumcheckFoldKnowledgeError`, in the shape the composition
  theorems produce. Each has its averaged form `…_rbrKnowledgeSoundness`.
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

section IteratedSumcheckFoldComposition

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! ### Perfect completeness -/

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- Perfect completeness of the `bIdx`-th non-last block, from the strict round relation at its
first round to the strict round relation at the first round of the next block. -/
theorem nonLastSingleBlockOracleReduction_perfectCompleteness (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (oracleReduction := nonLastSingleBlockOracleReduction 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) bIdx) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (nonLastSingleBlockFoldRelayGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) bIdx)
    (OracleVerifier.castIdxGuardedForm rfl (nonLastSingleBlockCommitIdx_succ bIdx)
      (foldCommitOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly) (nonLastSingleBlockCommitIdx bIdx)
        (isCommitmentRoundOfNonLastBlock (r := r) (𝓡 := 𝓡) bIdx)))
    (fun _ => Or.inl inferInstance)
    (OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers _ _ _ _ _
      (fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
      _ (fun _ => inferInstance)
      (fun i => foldRelayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt)))
      (fun i _ => foldRelayOracleReduction_perfectCompleteness 𝔽q β
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt))))
    (fun _ => OracleReduction.castIdx_perfectCompleteness
      (relIn := fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      (relOut := fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      rfl (nonLastSingleBlockCommitIdx_succ bIdx)
      (foldCommitOracleReduction_perfectCompleteness 𝔽q β (nonLastSingleBlockCommitIdx bIdx)
        (isCommitmentRoundOfNonLastBlock (r := r) (𝓡 := 𝓡) bIdx)))

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- Perfect completeness of the last block, from the strict round relation at its first round to
the strict round relation at round `ℓ`. -/
theorem lastBlockOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ))
      (oracleReduction := lastBlockOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly)) :=
  OracleReduction.castIdx_perfectCompleteness
    (relIn := fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (relOut := fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    lastBlockStartIdx_eq lastBlockEndIdx_eq
    (OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers _ _ _ _ _
      (fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩)
      _ (fun _ => inferInstance)
      (fun i => foldRelayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i))
      (fun i _ => foldRelayOracleReduction_perfectCompleteness 𝔽q β
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i)))

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- Perfect completeness of the non-last blocks, from the strict round relation at round `0` to
the strict round relation at the first round of the last block. -/
theorem nonLastBlocksOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (oracleReduction := nonLastBlocksOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly)) :=
  OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers _ _ _ _ _
    (fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    _ (fun _ => inferInstance)
    (fun bIdx => nonLastSingleBlockOracleVerifierGuardedForm 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) bIdx)
    (fun bIdx _ => nonLastSingleBlockOracleReduction_perfectCompleteness 𝔽q β bIdx)

omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- Perfect completeness of the sum-check-and-fold rounds, from the strict round relation at
round `0` to the strict round relation at round `ℓ`. -/
theorem sumcheckFoldOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ))
      (oracleReduction := sumcheckFoldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly)) :=
  OracleReduction.castIdx_perfectCompleteness
    (relIn := fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (relOut := fun i => strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (fin_zero_mul_eq (ϑ := ϑ) _) rfl
    (OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
      (nonLastBlocksOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly))
      (lastBlockOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly))
      (fun _ => Or.inl inferInstance)
      (nonLastBlocksOracleReduction_perfectCompleteness 𝔽q β)
      (fun _ => lastBlockOracleReduction_perfectCompleteness 𝔽q β))

/-! ### Round-by-round knowledge soundness -/

/-- The round-by-round knowledge error of the last block: each challenge carries the error of the
fold-relay round it belongs to. -/
def lastBlockRbrKnowledgeError (k : (pSpecLastBlock (L := L) (ϑ := ϑ)).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨(ℓ / ϑ - 1) * ϑ + ij.1, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ ij.1⟩ ij.2

omit [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the last block, from the round relation at
its first round to the round relation at round `ℓ`, with error `lastBlockRbrKnowledgeError`. -/
theorem lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase :
    (lastBlockOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (Fin.last ℓ))
      (lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.castIdx_rbrKnowledgeSoundnessWorstCase
    (relIn := fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (relOut := fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    lastBlockStartIdx_eq lastBlockEndIdx_eq
    (OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded _ _ _
      (fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ _ (hx := Fin.is_le i)⟩) _
      (fun i => foldRelayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly)
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i)) _
      (fun i => foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
        (lastBlockIdx_isNeCommitmentRound i)))

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the last block: the averaged form of
`lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem lastBlockOracleVerifier_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (Fin.last ℓ))
      (lastBlockOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := multpoly))
      (rbrKnowledgeError := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β)

/-- The round-by-round knowledge error of the fold-relay rounds of the `bIdx`-th non-last block:
each challenge carries the error of the fold-relay round it belongs to. -/
def nonLastSingleBlockFoldRelayRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1))
    (k : (pSpecFoldRelaySequence (L := L) (n := ϑ - 1)).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨bIdx * ϑ + ij.1, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx ij.1⟩ ij.2

/-- The round-by-round knowledge error of the `bIdx`-th non-last block: that of its fold-relay
rounds, then that of its fold-commit round. -/
def nonLastSingleBlockRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1)) :
    (pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      bIdx).ChallengeIdx → ℝ≥0 :=
  Sum.elim
    (nonLastSingleBlockFoldRelayRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (nonLastSingleBlockCommitIdx bIdx)) ∘ ChallengeIdx.sumEquiv.symm

omit [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the `bIdx`-th non-last block, from the round
relation at its first round to the round relation at the first round of the next block, with
error `nonLastSingleBlockRbrKnowledgeError`. -/
theorem nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase
    (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) bIdx).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (nonLastSingleBlockRbrKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        bIdx) :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (nonLastSingleBlockFoldRelayGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) bIdx)
    (OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded _ _ _
      (fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩) _
      (fun i => foldRelayOracleVerifierGuardedForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt))) _
      (fun i => foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
        (isNeCommitmentRound (r := r) (𝓡 := 𝓡) bIdx i (hx := i.isLt))))
    (OracleVerifier.castIdx_rbrKnowledgeSoundnessWorstCase
      (relIn := fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      (relOut := fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      rfl (nonLastSingleBlockCommitIdx_succ bIdx)
      (foldCommitOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β
        (nonLastSingleBlockCommitIdx bIdx)
        (isCommitmentRoundOfNonLastBlock (r := r) (𝓡 := 𝓡) bIdx)))

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the `bIdx`-th non-last block: the averaged form of
`nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) bIdx).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨↑bIdx.castSucc * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.castSucc⟩)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨↑bIdx.succ * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ bIdx.succ⟩)
      (rbrKnowledgeError := nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β bIdx)

/-- The round-by-round knowledge error of the non-last blocks: each challenge carries the error of
the block it belongs to. -/
def nonLastBlocksRbrKnowledgeError
    (k : (pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) :
    ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ij.1 ij.2

omit [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the non-last blocks, from the round relation
at round `0` to the round relation at the first round of the last block, with error
`nonLastBlocksRbrKnowledgeError`. -/
theorem nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase :
    (nonLastBlocksOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded _ _ _
    (fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩) _
    (fun bIdx => nonLastSingleBlockOracleVerifierGuardedForm 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) bIdx) _
    (fun bIdx => nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β bIdx)

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the non-last blocks: the averaged form of
`nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem nonLastBlocksOracleVerifier_rbrKnowledgeSoundness :
    (nonLastBlocksOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) ⟨0 * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (ϑ := ϑ) 0⟩)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ 0 (hx := Nat.zero_le _)⟩)
      (rbrKnowledgeError := nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β)

/-- The round-by-round knowledge error of the sum-check-and-fold rounds: that of the non-last
blocks, then that of the last block. -/
def sumcheckFoldKnowledgeError :
    (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx → ℝ≥0 :=
  Sum.elim
    (nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ∘
    ChallengeIdx.sumEquiv.symm

omit [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the sum-check-and-fold rounds, from the
round relation at round `0` to the round relation at round `ℓ`, with error
`sumcheckFoldKnowledgeError`. -/
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase :
    (sumcheckFoldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) 0)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (Fin.last ℓ))
      (sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.castIdx_rbrKnowledgeSoundnessWorstCase
    (relIn := fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (relOut := fun i => roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (fin_zero_mul_eq (ϑ := ϑ) _) rfl
    (OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
      (nonLastBlocksOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multpoly))
      (nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β)
      (lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β))

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the sum-check-and-fold rounds: the averaged form of
`sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    (sumcheckFoldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ))
      (rbrKnowledgeError := sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β)

end IteratedSumcheckFoldComposition

end ComponentReductions

end
end Binius.BinaryBasefold.CoreInteraction
