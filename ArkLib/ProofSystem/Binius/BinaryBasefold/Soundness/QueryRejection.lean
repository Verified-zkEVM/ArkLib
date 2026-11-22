/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.BadBlocks

/-!
# Binary Basefold: rejection of a query that hits the disagreement set

Let `j*` be a block such that no block above it is bad and no folding bad event has occurred.
If the suffix of the query point `v` at the destination index of `j*` lies in the
disagreement set of the fold of the oracle of `j*` and the decoded next codeword, the repetition
at `v` rejects (`not_logicalCheckSingleRepetition_of_mem_disagreementSet`). The disagreement
propagates block by block: an accepting guard at block `j + 1` puts the suffix in the fiberwise
disagreement set of block `j + 1` and its decoded codeword, the absence of the folding bad event
keeps it in the disagreement set of the folds, and compliance identifies the fold of the decoded
codeword with the next decoded codeword. At the last block the next codeword is the constant
function of the final constant, so the final equality fails.

## Main statements

* `uniqueDecodingClose_queryBlockSourceIdx_of_not_isBadBlock`, `goodBlockCodeword`: a block that
is not
  bad has an oracle within the unique-decoding radius, and its decoded codeword.
* `isCompliant_getNextOracle_of_not_isBadBlock`, `isCompliant_finalConstant_of_not_isBadBlock`:
  a block that is not bad is compliant with the next oracle, or with the final constant.
* `not_foldingBadEvent_of_not_hasBlockBadEvent`: without a block bad event, no block has a
  folding bad event.
* `apply_queryBlockSourceSuffix_ne_goodBlockCodeword_succ`: the propagation step from block `j` to
  block `j + 1`.
* `not_logicalCheckSingleRepetition_of_mem_disagreementSet`: the rejection.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
  `not_logicalCheckSingleRepetition_of_mem_disagreementSet` is Lemma 4.26 (in the proof of
  Proposition 4.24), whose proof the propagation step follows.
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Probability
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
noncomputable section
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section QueryPhaseSoundnessStatements

open QueryPhase

/-- The oracle of a block that is not bad is within the unique-decoding radius at the block's
source index. -/
lemma uniqueDecodingClose_queryBlockSourceIdx_of_not_isBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (oStmtIn j) := by
  have h_close :=
    uniqueDecodingClose_of_not_isBadBlock (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn)
      (oStmtIn := oStmtIn) (j := j) h_good
      (destIdx := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_idx := rfl)
  simpa using h_close

/-- The decoded codeword of the oracle of a block that is not bad, at the block's source index. -/
abbrev goodBlockCodeword
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (queryBlockSourceIdx_le
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (f := oStmtIn j)
    (h_within_radius :=
      uniqueDecodingClose_queryBlockSourceIdx_of_not_isBadBlock (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good)

/-- If no block bad event exists at the last statement index, the folding bad event does not
occur at block `j`. -/
lemma not_foldingBadEvent_of_not_hasBlockBadEvent
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_no_bad_global : ¬ HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    ¬ FoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      ϑ
      (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f_i := oStmtIn j)
      (r_challenges :=
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
          (i := Fin.last ℓ) stmtIn.challenges (k := j.val * ϑ) (h := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := j))) := by
  intro h_bad
  apply h_no_bad_global
  refine ⟨j, ?_⟩
  have h_branch :
      oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ (Fin.last ℓ).val := by
    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
      (i := Fin.last ℓ) (j := j)
  unfold FoldingBadEventAtBlock
  rw [dite_eq_left h_branch]
  exact h_bad

/-- A block `j` that is not bad and not the last is compliant with the oracle of block `j + 1`. -/
lemma isCompliant_getNextOracle_of_not_isBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f_i := oStmtIn j)
      (f_i_plus_steps :=
        getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
            change j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
            exact hj)
          (destDomainIdx := queryBlockDestIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (h_destDomainIdx := by rfl))
      (challenges :=
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
          (i := Fin.last ℓ) stmtIn.challenges (k := j.val * ϑ) (h := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := j))) := by
  have h_good' := h_good
  have hj_div := hj
  simp only [nBlocks, toOutCodewordsCount_last] at hj_div
  simp only [IsBadBlock, hj_div, nBlocks, toOutCodewordsCount_last, not_not, ↓reduceDIte]
    at h_good' ⊢
  exact h_good'

/-- The last block, if not bad, is compliant with the constant function of the final constant. -/
lemma isCompliant_finalConstant_of_not_isBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : ¬ j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f_i := oStmtIn j)
      (f_i_plus_steps := fun _ => stmtIn.finalConstant)
      (challenges :=
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
          (i := Fin.last ℓ) stmtIn.challenges (k := j.val * ϑ) (h := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := j))) := by
  have h_j_eq : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = j := by
    apply Fin.ext
    have h_ge : nBlocks (ℓ := ℓ) (ϑ := ϑ) ≤ j.val + 1 := Nat.le_of_not_gt hj
    have h_lt : j.val < nBlocks (ℓ := ℓ) (ϑ := ϑ) := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_ge h_lt
    simp [getLastOraclePositionIndex, toOutCodewordsCount_last]
    omega
  have hj_div := hj
  simp only [nBlocks, toOutCodewordsCount_last] at hj_div
  simp only [IsBadBlock, hj_div, nBlocks, toOutCodewordsCount_last, not_not, ↓reduceDIte]
    at h_good ⊢
  cases h_j_eq
  exact h_good

/-- `goodBlockCodeword` is the decoded codeword obtained through fiberwise closeness. -/
lemma goodBlockCodeword_eq_of_fiberwiseClose
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    (h_fw : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ) (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j)) :
    goodBlockCodeword (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good =
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j)
      (h_within_radius :=
        uniqueDecodingClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (steps := ϑ)
          (h_destIdx := by rfl)
          (h_destIdx_le := queryBlockDestIdx_le
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (f := oStmtIn j) h_fw) := by
  rfl

/-- If the oracle of block `j` and `g` differ at the source suffix of `v`, the destination suffix
of `v` is in their fiberwise disagreement set. -/
lemma queryBlockDestSuffix_mem_fiberwiseDisagreementSet
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j))
    (h_point_ne :
      (oStmtIn j)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) ≠
      g
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v)) :
    queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v ∈
    fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      ϑ (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (oStmtIn j) g := by
  simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v,
    iteratedQuotientMap_queryBlockSourceSuffix
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ) (ϑ := ϑ) (j := j) (v := v),
    h_point_ne⟩

/-- The next oracle's decoded value agrees with the next good block's codeword. -/
private theorem uniqueDecodingCodeword_getNextOracle_apply_eq_goodBlockCodeword
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (hgood : ¬ IsBadBlock 𝔽q β stmtIn oStmtIn ⟨j.val + 1, hj⟩)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (hclose : UniqueDecodingClose 𝔽q β (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
      (getNextOracle 𝔽q β (ϑ := ϑ) (i := Fin.last ℓ) (oStmt := oStmtIn)
        (j := j) (hj := hj) (destDomainIdx := queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j) (h_destDomainIdx := rfl))) :
    uniqueDecodingCodeword 𝔽q β (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
      (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
      (f := getNextOracle 𝔽q β (ϑ := ϑ) (i := Fin.last ℓ) (oStmt := oStmtIn)
        (j := j) (hj := hj) (destDomainIdx := queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j) (h_destDomainIdx := rfl))
      (h_within_radius := hclose) (queryBlockDestSuffix 𝔽q β j v) =
    goodBlockCodeword 𝔽q β stmtIn oStmtIn ⟨j.val + 1, hj⟩ hgood
      (queryBlockSourceSuffix 𝔽q β ⟨j.val + 1, hj⟩ v) := by
  have hget := getNextOracle_eq_oracleStatement (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) (j := j) (hj := hj)
  have hclose' := uniqueDecodingClose_congr (𝔽q := 𝔽q) (β := β)
    rfl (heq_of_eq hget) hclose
  have hdecoded := uniqueDecodingCodeword_eval_eq_of_fin_eq 𝔽q β
    (hi := queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
    (hj := queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
    rfl (heq_of_eq hget) hclose (queryBlockDestSuffix 𝔽q β j v)
  have hnext := uniqueDecodingClose_queryBlockSourceIdx_of_not_isBadBlock 𝔽q β
    stmtIn oStmtIn ⟨j.val + 1, hj⟩ hgood
  have htransport := uniqueDecodingCodeword_queryBlockDestIdx_eq_queryBlockSourceIdx_succ 𝔽q β
    oStmtIn j hj v hclose' hnext
  dsimp only at htransport hdecoded
  rw [← queryBlockDestSuffix_eq_queryBlockSourceSuffix_succ
    (𝔽q := 𝔽q) (β := β) (j := j) (hj := hj) (v := v)] at htransport
  exact hdecoded.trans htransport

/-- A disagreement at a good last block makes its computed fold differ from the final constant. -/
private theorem logicalComputeFoldedValue_ne_finalConstant_of_goodLastBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hlast : ¬ j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (hgood : ¬ IsBadBlock 𝔽q β stmtIn oStmtIn j)
    (hno : ¬ HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (hpoint : oStmtIn j (queryBlockSourceSuffix 𝔽q β j v) ≠
      goodBlockCodeword 𝔽q β stmtIn oStmtIn j hgood (queryBlockSourceSuffix 𝔽q β j v)) :
    logicalComputeFoldedValue 𝔽q β (queryBlockIdx j) v stmtIn
      (logicalQueryFiberPoints 𝔽q β oStmtIn (queryBlockIdx j) v) ≠ stmtIn.finalConstant := by
  obtain ⟨hfw, hclose, hfold⟩ :=
    isCompliant_finalConstant_of_not_isBadBlock 𝔽q β stmtIn oStmtIn j hlast hgood
  rw [goodBlockCodeword_eq_of_fiberwiseClose 𝔽q β stmtIn oStmtIn j hgood hfw] at hpoint
  have hmem := queryBlockDestSuffix_mem_fiberwiseDisagreementSet 𝔽q β oStmtIn j v _ hpoint
  have hsubset := not_foldingBadEvent_of_not_hasBlockBadEvent 𝔽q β
    oStmtIn stmtIn j hno
  unfold FoldingBadEvent at hsubset
  simp only [hfw, not_not, ↓reduceDIte] at hsubset
  have hdisagree := hsubset hmem
  simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
    at hdisagree
  have heval := logicalComputeFoldedValue_eq_iteratedFold 𝔽q β
    (oStmt := oStmtIn) (k := queryBlockIdx j) (v := v) (stmt := stmtIn)
  have hconstant : uniqueDecodingCodeword 𝔽q β
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
      (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j)
      (f := fun _ => stmtIn.finalConstant) (h_within_radius := hclose)
      (queryBlockDestSuffix 𝔽q β j v) = stmtIn.finalConstant := by
    rw [uniqueDecodingCodeword_const]
  intro h
  apply hdisagree
  exact heval.symm.trans
    (h.trans (hconstant.symm.trans (congrFun hfold (queryBlockDestSuffix 𝔽q β j v)).symm))

variable [DecidableEq 𝔽q]

/-- The propagation step. Let blocks `j` and `j + 1` not be bad, let no block bad event exist,
and let the repetition at `v` accept. If the oracle of block `j` differs from its decoded
codeword at the source suffix of `v`, the same holds for block `j + 1`. -/
lemma apply_queryBlockSourceSuffix_ne_goodBlockCodeword_succ
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    (h_next_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      stmtIn oStmtIn ⟨j.val + 1, hj⟩)
    (h_no_bad_global : ¬ HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_accept : LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      oStmtIn v stmtIn stmtIn.finalConstant)
    (h_point_ne :
      (oStmtIn j)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) ≠
      goodBlockCodeword (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v)) :
    let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
    (oStmtIn j_next)
      (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) ≠
    goodBlockCodeword (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_next) h_next_good
      (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
  dsimp only
  let next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
  obtain ⟨hfw, hclose, hfold⟩ :=
    isCompliant_getNextOracle_of_not_isBadBlock 𝔽q β stmtIn oStmtIn j hj h_good
  have hpoint := h_point_ne
  rw [goodBlockCodeword_eq_of_fiberwiseClose 𝔽q β stmtIn oStmtIn j h_good hfw] at hpoint
  have hmem := queryBlockDestSuffix_mem_fiberwiseDisagreementSet 𝔽q β oStmtIn j v _ hpoint
  have hsubset := not_foldingBadEvent_of_not_hasBlockBadEvent 𝔽q β
    oStmtIn stmtIn j h_no_bad_global
  unfold FoldingBadEvent at hsubset
  simp only [hfw, not_not, ↓reduceDIte] at hsubset
  have hdisagree := hsubset hmem
  simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
    at hdisagree
  have heval := logicalComputeFoldedValue_eq_iteratedFold 𝔽q β
    (oStmt := oStmtIn) (k := queryBlockIdx j) (v := v) (stmt := stmtIn)
  have hguard : logicalComputeFoldedValue 𝔽q β (queryBlockIdx j) v stmtIn
      (logicalQueryFiberPoints 𝔽q β oStmtIn (queryBlockIdx j) v) =
      oStmtIn next (queryBlockSourceSuffix 𝔽q β next v) := by
    have h := logicalComputeFoldedValue_eq_of_logicalCheckSingleRepetition 𝔽q β
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v) (h_accept := h_accept)
      (j := next) (by dsimp [next]; omega)
    simpa only [next, queryBlockIdx, Nat.add_sub_cancel] using h
  have hdecoded := uniqueDecodingCodeword_getNextOracle_apply_eq_goodBlockCodeword 𝔽q β
    stmtIn oStmtIn j hj h_next_good v hclose
  intro h
  apply hdisagree
  exact heval.symm.trans
    (hguard.trans (h.trans (hdecoded.symm.trans
      (congrFun hfold (queryBlockDestSuffix 𝔽q β j v)).symm)))

/-- Disagreement with decoded codewords propagates along a range of compliant blocks. -/
private theorem point_ne_goodBlockCodeword_of_le
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_accept : LogicalCheckSingleRepetition 𝔽q β oStmtIn v stmtIn stmtIn.finalConstant)
    (h_no_bad_global : ¬ HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (first last : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) (hle : first.val ≤ last.val)
    (hgood : ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)), first.val ≤ j.val →
      ¬ IsBadBlock 𝔽q β stmtIn oStmtIn j)
    (hfirst : oStmtIn first (queryBlockSourceSuffix 𝔽q β first v) ≠
      goodBlockCodeword 𝔽q β stmtIn oStmtIn first (hgood first le_rfl)
        (queryBlockSourceSuffix 𝔽q β first v)) :
    oStmtIn last (queryBlockSourceSuffix 𝔽q β last v) ≠
      goodBlockCodeword 𝔽q β stmtIn oStmtIn last (hgood last hle)
        (queryBlockSourceSuffix 𝔽q β last v) := by
  have propagate (n : ℕ) (hn : first.val ≤ n) :
      ∀ hb : n < nBlocks (ℓ := ℓ) (ϑ := ϑ),
        oStmtIn ⟨n, hb⟩ (queryBlockSourceSuffix 𝔽q β ⟨n, hb⟩ v) ≠
          goodBlockCodeword 𝔽q β stmtIn oStmtIn ⟨n, hb⟩ (hgood ⟨n, hb⟩ hn)
            (queryBlockSourceSuffix 𝔽q β ⟨n, hb⟩ v) := by
    induction n, hn using Nat.le_induction with
    | base =>
      intro hb
      exact hfirst
    | succ n hn ih =>
      intro hb
      have hprev : n < nBlocks (ℓ := ℓ) (ϑ := ϑ) := by omega
      exact apply_queryBlockSourceSuffix_ne_goodBlockCodeword_succ 𝔽q β
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := ⟨n, hprev⟩) (hj := hb)
        (h_good := hgood ⟨n, hprev⟩ hn) (h_next_good := hgood ⟨n + 1, hb⟩ (by simp only; omega))
        (h_no_bad_global := h_no_bad_global) (v := v) (h_accept := h_accept)
        (h_point_ne := ih hprev)
  exact propagate last.val hle last.isLt

/-- A suffix disagreement propagates through the later good blocks to the final fold. -/
private theorem logicalComputeFoldedValue_last_ne_finalConstant_of_mem_disagreementSet
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    -- Block index j* ∈ {0, ..., ℓ/ϑ - 1} (the highest non-compliant block)
    (j_star : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star))
    (h_f_next_shape :
      (∃ hj : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ),
        f_next =
          getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
              change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
              exact hj)
            (destDomainIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
            (h_destDomainIdx := by rfl))
      ∨ (¬ j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) ∧
          f_next = fun _ => stmtIn.finalConstant))
    (h_next_close : UniqueDecodingClose 𝔽q β
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) f_next)
    -- All blocks after j* are compliant (consequence of maximality of j*)
    (h_good_after : ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)), j_star < j →
      ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    -- No bad events globally (for the inductive step at subsequent blocks)
    (h_no_bad_global : ¬ HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    let f_star := oStmtIn j_star
    let folded_f := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) ϑ rfl
      (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) f_star
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        stmtIn.challenges (k := j_star.val * ϑ)
        (oracle_index_add_steps_le_ℓ (i := Fin.last ℓ) (j := j_star)))
    let f_bar_next := uniqueDecodingCodeword 𝔽q β
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
      (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
      (f := f_next) (h_within_radius := h_next_close)
    let v_suffix :=
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
        (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
        (k := (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star).val)
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, zero_mod, zero_add])
        (h_destIdx_le := (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)) (x := v)
    v_suffix ∈ disagreementSet 𝔽q β
      (i := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
      (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) (h_destIdx := rfl)
      (f := folded_f) (g := f_bar_next) →
    LogicalCheckSingleRepetition 𝔽q β oStmtIn v stmtIn stmtIn.finalConstant →
    logicalComputeFoldedValue 𝔽q β
      ⟨ℓ / ϑ - 1, Nat.sub_lt (Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)) zero_lt_one⟩
      v stmtIn (logicalQueryFiberPoints 𝔽q β oStmtIn
        ⟨ℓ / ϑ - 1, Nat.sub_lt (Nat.div_pos
          (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)) zero_lt_one⟩ v)
      ≠ stmtIn.finalConstant := by
  intro f_star folded_f f_bar_next v_suffix h_disagree h_accept
  have hpos : 0 < ℓ / ϑ :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
  have hjlt : j_star.val < ℓ / ϑ := by
    simpa only [nBlocks, toOutCodewordsCount_last] using j_star.isLt
  let last : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨ℓ / ϑ - 1, by
    simpa only [nBlocks, toOutCodewordsCount_last] using Nat.sub_lt hpos zero_lt_one⟩
  have hbase : logicalComputeFoldedValue 𝔽q β (queryBlockIdx j_star) v stmtIn
      (logicalQueryFiberPoints 𝔽q β oStmtIn (queryBlockIdx j_star) v) ≠
      f_bar_next v_suffix := by
    have heval := logicalComputeFoldedValue_eq_iteratedFold 𝔽q β
      (oStmt := oStmtIn) (k := queryBlockIdx j_star) (v := v) (stmt := stmtIn)
    have hd : folded_f v_suffix ≠ f_bar_next v_suffix := by
      simpa only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
        using h_disagree
    exact fun h => hd (heval.symm.trans h)
  by_cases hmore : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
  · let next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_star.val + 1, hmore⟩
    have hgood : ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)), next.val ≤ j.val →
        ¬ IsBadBlock 𝔽q β stmtIn oStmtIn j := by
      intro j hj
      exact h_good_after j (Fin.lt_def.mpr (by dsimp [next] at hj; omega))
    have hshape : f_next = getNextOracle 𝔽q β (ϑ := ϑ) (i := Fin.last ℓ)
        (oStmt := oStmtIn) (j := j_star) (hj := hmore)
        (destDomainIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
        (h_destDomainIdx := rfl) := by
      rcases h_f_next_shape with h | h
      · exact h.2
      · exact (h.1 hmore).elim
    have hdecoded : f_bar_next v_suffix =
        goodBlockCodeword 𝔽q β stmtIn oStmtIn next (hgood next le_rfl)
          (queryBlockSourceSuffix 𝔽q β next v) := by
      dsimp only [f_bar_next]
      cases hshape
      exact uniqueDecodingCodeword_getNextOracle_apply_eq_goodBlockCodeword 𝔽q β
        stmtIn oStmtIn j_star hmore (hgood next le_rfl) v h_next_close
    have hguard := logicalComputeFoldedValue_eq_of_logicalCheckSingleRepetition 𝔽q β
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v) (h_accept := h_accept)
      (j := next) (by dsimp [next]; omega)
    have hfirst : oStmtIn next (queryBlockSourceSuffix 𝔽q β next v) ≠
        goodBlockCodeword 𝔽q β stmtIn oStmtIn next (hgood next le_rfl)
          (queryBlockSourceSuffix 𝔽q β next v) := by
      intro h
      apply hbase
      exact hguard.trans (h.trans hdecoded.symm)
    have hle : next.val ≤ last.val := by
      have hm := hmore
      simp only [nBlocks, toOutCodewordsCount_last] at hm
      dsimp [next, last]
      omega
    have hlastPoint := point_ne_goodBlockCodeword_of_le 𝔽q β stmtIn oStmtIn v
      h_accept h_no_bad_global next last hle hgood hfirst
    exact logicalComputeFoldedValue_ne_finalConstant_of_goodLastBlock 𝔽q β
      stmtIn oStmtIn last (by simp only [last, nBlocks, toOutCodewordsCount_last]; omega)
      (hgood last hle) h_no_bad_global v hlastPoint
  · have hshape : f_next = fun _ => stmtIn.finalConstant := by
      rcases h_f_next_shape with h | h
      · exact (hmore h.1).elim
      · exact h.2
    have hconstant : f_bar_next = fun _ => stmtIn.finalConstant := by
      dsimp only [f_bar_next]
      cases hshape
      exact uniqueDecodingCodeword_const 𝔽q β
        (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
        (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) stmtIn.finalConstant
    have hlast : (queryBlockIdx j_star : Fin (ℓ / ϑ)) = ⟨ℓ / ϑ - 1, by omega⟩ := by
      apply Fin.ext
      have hm := hmore
      simp only [nBlocks, toOutCodewordsCount_last] at hm
      change j_star.val = ℓ / ϑ - 1
      omega
    rw [hconstant] at hbase
    rw [← hlast]
    exact hbase

/-- Let `f_next` be the oracle of block `j* + 1`, or the constant function of the final constant
if `j*` is the last block, and let it be within the unique-decoding radius. Let no block above
`j*` be bad, and let no block bad event occur. If the
suffix of `v` at `j*·ϑ + ϑ` lies in the disagreement set of the fold of the oracle of `j*` and the
decoded codeword of `f_next`, the repetition at `v` rejects.

The proof is an induction over the blocks above `j*`: in an accepting repetition the value carried
into each later block differs from the decoded codeword there, so the final equality fails. -/
theorem not_logicalCheckSingleRepetition_of_mem_disagreementSet
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    -- Block index j* ∈ {0, ..., ℓ/ϑ - 1} (the highest non-compliant block)
    (j_star : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star))
    (h_f_next_shape :
      (∃ hj : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ),
        f_next =
          getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
              change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
              exact hj)
            (destDomainIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
            (h_destDomainIdx := by rfl))
      ∨ (¬ j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) ∧
          f_next = fun _ => stmtIn.finalConstant))
    (h_next_close : UniqueDecodingClose 𝔽q β
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) f_next)
    -- All blocks after j* are compliant (consequence of maximality of j*)
    (h_good_after : ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)), j_star < j →
      ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    -- No bad events globally (for the inductive step at subsequent blocks)
    (h_no_bad_global : ¬ HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    let f_star := oStmtIn j_star
    let folded_f := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) ϑ rfl
      (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) f_star
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        stmtIn.challenges (k := j_star.val * ϑ)
        (oracle_index_add_steps_le_ℓ (i := Fin.last ℓ) (j := j_star)))
    let f_bar_next := uniqueDecodingCodeword 𝔽q β
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
      (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
      (f := f_next) (h_within_radius := h_next_close)
    let v_suffix :=
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
        (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
        (k := (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star).val)
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, zero_mod, zero_add])
        (h_destIdx_le := (queryBlockDestIdx_le (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)) (x := v)
    v_suffix ∈ disagreementSet 𝔽q β
      (i := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star)
      (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star) (h_destIdx := rfl)
      (f := folded_f) (g := f_bar_next) →
    ¬ LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.finalConstant := by
  intro f_star folded_f f_bar_next v_suffix h_disagree h_accept
  have h_div_pos : 0 < ℓ / ϑ :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
  have h_final := h_accept (⟨ℓ / ϑ, by omega⟩ : Fin (ℓ / ϑ + 1))
  unfold LogicalStepCondition at h_final
  split_ifs at h_final with h_absurd
  · exact absurd h_absurd (lt_irrefl _)
  exact logicalComputeFoldedValue_last_ne_finalConstant_of_mem_disagreementSet 𝔽q β stmtIn
    oStmtIn j_star f_next
    h_f_next_shape h_next_close h_good_after h_no_bad_global v h_disagree h_accept h_final

end QueryPhaseSoundnessStatements

end

end Binius.BinaryBasefold
