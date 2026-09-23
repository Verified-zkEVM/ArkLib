/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module


public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.BadBlocks
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.FoldDistance

/-!
## Binary Basefold Soundness Query Phase Theorems

Final query-phase rejection and probability bounds for the Binary Basefold soundness proof.
This file packages:
1. Lemma 4.26, which turns disagreement on the terminal suffix into query rejection
2. Proposition 4.24 for the single-repetition proximity-check bound
3. the final query-phase probability statements built from the bad-block analysis

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
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
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section QueryPhaseSoundnessStatements

open QueryPhase

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] in
lemma goodBlock_implies_currentUDRClose
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (oStmtIn j) := by
  classical
  have h_close :=
    goodBlock_implies_UDRClose (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn)
      (oStmtIn := oStmtIn) (j := j) h_good
      (destIdx := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_idx := rfl)
      (h_le := queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
  simpa using h_close

abbrev goodBlockCodeword
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (queryBlockSourceIdx_le
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (f := oStmtIn j)
    (h_within_radius :=
      goodBlock_implies_currentUDRClose (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] in
lemma no_foldingBadEvent_of_no_bad_global
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_no_bad_global : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    ¬ foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
  have h_bad' := h_bad
  set_option backward.isDefEq.respectTransparency false in
    simp only [foldingBadEventAtBlock, h_branch] at h_bad' ⊢
  exact h_bad'

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] in
lemma goodBlock_intermediate_isCompliant
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
  simp only [badBlockProp, hj_div, nBlocks, toOutCodewordsCount_last, not_not, ↓reduceDIte]
    at h_good' ⊢
  exact h_good'

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] in
lemma goodBlock_last_isCompliant
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : ¬ j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j) :
    isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f_i := oStmtIn j)
      (f_i_plus_steps := fun _ => stmtIn.final_constant)
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
  simp only [badBlockProp, hj_div, nBlocks, toOutCodewordsCount_last, not_not, ↓reduceDIte]
    at h_good ⊢
  cases h_j_eq
  exact h_good

omit [CharP L 2] [DecidableEq 𝔽q] [SampleableType L] in
lemma goodBlockCodeword_eq_of_fiberwiseClose
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    (h_fw : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ) (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j)) :
    goodBlockCodeword (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good =
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j)
      (h_within_radius :=
        UDRClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (steps := ϑ)
          (h_destIdx := by rfl)
          (h_destIdx_le := queryBlockDestIdx_le
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (f := oStmtIn j) h_fw) := by
  exact
    UDRCodeword_eq_of_close (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_i := queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j)
      (goodBlock_implies_currentUDRClose (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good)
      (UDRClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (steps := ϑ)
        (h_destIdx := by rfl)
        (h_destIdx_le := queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (f := oStmtIn j) h_fw)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] in
lemma point_disagreement_mem_fiberwiseDisagreement
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
  classical
  simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v,
    queryBlockSourceSuffix_maps_to_destSuffix
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ) (ϑ := ϑ) (j := j) (v := v),
    h_point_ne⟩

omit [CharP L 2] [SampleableType L] in
lemma goodBlock_point_disagreement_step
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    (h_next_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      stmtIn oStmtIn ⟨j.val + 1, hj⟩)
    (h_no_bad_global : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_accept : logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      oStmtIn v stmtIn stmtIn.final_constant)
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
  let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
  let h_cur_close :=
    goodBlock_implies_currentUDRClose (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good
  let f_bar_cur :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j) (h_within_radius := h_cur_close)
  let h_next_close :=
    goodBlock_implies_currentUDRClose (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_next) h_next_good
  let f_bar_next :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (f := oStmtIn j_next) (h_within_radius := h_next_close)
  dsimp only [j_next, goodBlockCodeword]
  have h_compliant :=
    goodBlock_intermediate_isCompliant (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) (hj := hj) h_good
  rcases h_compliant with ⟨h_fw, h_next_close_raw, h_fold_eq_raw⟩
  have h_no_bad_local :=
    no_foldingBadEvent_of_no_bad_global (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (stmtIn := stmtIn) (j := j) h_no_bad_global
  have h_f_bar_cur_eq :=
    goodBlockCodeword_eq_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j) h_good h_fw
  have h_point_ne_raw := h_point_ne
  rw [h_f_bar_cur_eq] at h_point_ne_raw
  let f_bar_cur_raw :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := oStmtIn j)
      (h_within_radius :=
        UDRClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (steps := ϑ)
          (h_destIdx := by rfl)
          (h_destIdx_le := queryBlockDestIdx_le
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (f := oStmtIn j) h_fw)
  have h_mem_fiber :
      queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v ∈
    fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        ϑ (h_destIdx := by rfl)
        (h_destIdx_le := queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (oStmtIn j)
        (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (queryBlockSourceIdx_le
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (f := oStmtIn j)
          (h_within_radius :=
            UDRClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := queryBlockSourceIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
              (steps := ϑ)
              (h_destIdx := by rfl)
              (h_destIdx_le := queryBlockDestIdx_le
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
              (f := oStmtIn j) h_fw)) :=
    point_disagreement_mem_fiberwiseDisagreement
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (ℓ := ℓ) (ϑ := ϑ) (j := j) (v := v)
      (g := f_bar_cur_raw)
      h_point_ne_raw
  have h_subset := h_no_bad_local
  unfold foldingBadEvent at h_subset
  simp only [h_fw, not_not, ↓reduceDIte] at h_subset
  have h_mem_disagree := h_subset h_mem_fiber
  have h_fold_eq := h_fold_eq_raw
  dsimp only at h_fold_eq
  have h_eval_eq :=
    logical_computeFoldedValue_eq_iterated_fold (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmt := oStmtIn)
      (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)
      (v := v) (stmt := stmtIn)
  have h_eval_ne_raw :
      logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v stmtIn
        (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v) ≠
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (f := getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
            change j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
            exact hj)
          (destDomainIdx := queryBlockDestIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (h_destDomainIdx := by rfl))
        (h_within_radius := h_next_close_raw)
        (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) := by
    have h_mem_disagree' := h_mem_disagree
    simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
      at h_mem_disagree'
    intro h_eq
    apply h_mem_disagree'
    have h_fold_eq_eval :=
      congrFun h_fold_eq
        (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v)
    have h_suffix_eq :
        getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v) =
        queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v := by
      rfl
    rw [h_suffix_eq] at h_eval_eq
    exact h_eval_eq.symm.trans (h_eq.trans h_fold_eq_eval.symm)
  have h_pos_next : 0 < j_next.val := by
    dsimp only [j_next]
    omega
  have h_guard_next :=
    logical_checkSingleRepetition_guard_eq (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
      (h_accept := h_accept) (j := j_next) h_pos_next
  dsimp only [j_next] at h_guard_next
  have h_prev_idx_eq :
      (⟨j.val + 1 - 1, by
        have h_lt := hj
        simp only [nBlocks, toOutCodewordsCount_last] at h_lt
        omega⟩ : Fin (ℓ / ϑ)) =
      queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j := by
    apply Fin.eq_of_val_eq
    exact Nat.add_sub_cancel j.val 1
  rw [h_prev_idx_eq] at h_guard_next
  have h_idx_eq :=
    queryBlockDestIdx_eq_queryBlockSourceIdx_succ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)
  have h_getNext_eq :
      getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
        (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
          change j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
          exact hj)
        (destDomainIdx := queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (h_destDomainIdx := by rfl) =
      fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y) := by
    funext y
    unfold getNextOracle
    simp only
    dsimp only [j_next]
  have h_next_close_stmt :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y)) := by
    rw [← h_getNext_eq]
    exact h_next_close_raw
  have h_point_ne_stmt :
      (oStmtIn j_next)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) ≠
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (f := fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y))
        (h_within_radius := h_next_close_stmt)
        (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) := by
    intro h_eq
    apply h_eval_ne_raw
    rw [h_guard_next]
    dsimp only [j_next] at h_eq ⊢
    have h_codeword_raw_eq :
          UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (queryBlockDestIdx
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
            (queryBlockDestIdx_le
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
            (f := getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
              (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
                change j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
                exact hj)
              (destDomainIdx := queryBlockDestIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
              (h_destDomainIdx := by rfl))
            (h_within_radius := h_next_close_raw)
            (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) =
          UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (queryBlockDestIdx
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
            (queryBlockDestIdx_le
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
            (f := fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y))
            (h_within_radius := h_next_close_stmt)
            (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) := by
        simp only [h_getNext_eq]
    exact h_eq.trans h_codeword_raw_eq.symm
  have h_point_ne_transport := h_point_ne_stmt
  rw [queryBlockDestSuffix_eq_queryBlockSourceSuffix_succ
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj) (v := v)] at h_point_ne_transport
  have h_codeword_transport_eval :=
    successor_codeword_eval_eq (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ) (ϑ := ϑ)
      (oStmtIn := oStmtIn) (j := j) (hj := hj) (v := v)
      (h_next_close_stmt := by
        dsimp only [j_next]
        exact h_next_close_stmt)
      (h_next_close := by
        dsimp only [j_next]
        exact h_next_close)
  dsimp only [j_next] at h_codeword_transport_eval
  intro h_eq
  apply h_point_ne_transport
  exact h_eq.trans h_codeword_transport_eval.symm

omit [CharP L 2] [SampleableType L] in
/-- **Lemma 4.26** (Query rejection from disagreement suffix).

If the verifier's query point `v` has its suffix in the disagreement set between
`fold(f^{(j*\cdot\vartheta)})` and `\bar f^{(j*\cdot\vartheta+\vartheta)}`, then the
single-repetition logical check rejects.

**Hypotheses (following BinaryBasefold.md, Lemma 4.26):**
- `h_no_bad_event`: The bad event at block `j*` didn't occur.
- `h_good_after`: All blocks after `j*` are compliant (maximality of `j*`).
- `h_no_bad_global`: No bad events occur at any block (for the inductive step).

**Proof sketch (per spec):**
- **Base case (i = j*\cdot\vartheta):** `V` computes the fold inline.
  Since the suffix is in the disagreement set, the folded value differs from the codeword.
- **Inductive step (i > j*\cdot\vartheta):** Disagreement propagates using no-bad-events
  and compliance of subsequent blocks.
- **Final step:** The final check fails. -/
theorem lemma_4_26_reject_if_suffix_in_disagreement
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    -- Block index j* ∈ {0, ..., ℓ/ϑ - 1} (the highest non-compliant block)
    (j_star : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    {destIdx : Fin r} (h_destIdx : destIdx.val = j_star.val * ϑ + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin ϑ → L)
    (h_r_challenges :
      r_challenges =
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
          stmtIn.challenges (k := j_star.val * ϑ) (h := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := j_star)))
    (h_f_next_shape :
      (∃ hj : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ),
        f_next =
          getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
              change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
              exact hj)
            (destDomainIdx := destIdx) (h_destDomainIdx := by
              exact h_destIdx))
      ∨ (¬ j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) ∧
          f_next = fun _ => stmtIn.final_constant))
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β (i := ⟨j_star.val * ϑ, by omega⟩) ϑ
      h_destIdx h_destIdx_le (oStmtIn j_star) r_challenges)
    (h_next_close : UDRClose 𝔽q β destIdx h_destIdx_le f_next)
    -- All blocks after j* are compliant (consequence of maximality of j*)
    (h_good_after : ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)), j_star < j →
      ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    -- No bad events globally (for the inductive step at subsequent blocks)
    (h_no_bad_global : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    let f_star := oStmtIn j_star
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨j_star.val * ϑ, by omega⟩ ϑ h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
    let f_bar_next := UDRCodeword 𝔽q β destIdx h_destIdx_le
      (f := f_next) (h_within_radius := h_next_close)
    let v_suffix :=
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r)) (destIdx := destIdx)
        (k := destIdx.val)
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, zero_mod, zero_add])
        (h_destIdx_le := h_destIdx_le) (x := v)
    v_suffix ∈ disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
      (f := folded_f) (g := f_bar_next) →
    ¬ logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant := by
  classical
  -- Proof per BinaryBasefold.md, Lemma 4.26.
  -- We show: assuming all step conditions pass, the fold value at the last step
  -- disagrees with `final_constant`, contradicting the final step condition.
  -- Introduce the let bindings and hypotheses
  intro f_star folded_f f_bar_next v_suffix h_disagree h_accept
  have h_destIdx_le' : j_star.val * ϑ + ϑ ≤ ℓ := by
    rw [h_destIdx] at h_destIdx_le
    exact h_destIdx_le
  have h_destIdx_eq :
      destIdx =
        ⟨j_star.val * ϑ + ϑ, by
          exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx_le'⟩ := by
    apply Fin.eq_of_val_eq
    exact h_destIdx
  cases h_destIdx_eq
  -- Step 1: Extract the final step condition from h_accept.
  -- At k = ℓ/ϑ (the terminal index), the step condition says:
  --   fold(oStmt(ℓ/ϑ-1), ...)(v_ℓ) = final_constant
  have h_div_pos : ℓ / ϑ > 0 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
  have h_final := h_accept (⟨ℓ / ϑ, by omega⟩ : Fin (ℓ / ϑ + 1))
  unfold logical_stepCondition at h_final
  split_ifs at h_final with h_absurd
  · exact absurd h_absurd (lt_irrefl _)
  have h_j_star_lt_div : j_star.val < ℓ / ϑ := by
    have h_lt := j_star.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    exact h_lt
  let j_star_idx : Fin (ℓ / ϑ) := ⟨j_star.val, h_j_star_lt_div⟩
  -- Step 2: Key inductive invariant — disagreement propagates from j* to the final step.
  -- For each block k from j_star to ℓ/ϑ - 1 (inclusive), conditioned on all guard checks
  -- in h_accept passing, the fold value computed by the verifier at step k disagrees with
  -- the closest codeword at the next level.
  --
  -- At k = ℓ/ϑ - 1 (the last block), this gives:
  --   fold(oStmt(ℓ/ϑ-1), ...)(v_ℓ) ≠ final_constant
  --
  -- The induction proceeds as follows (per the spec):
  -- Base case (k = j*): The fold value = iterated_fold(oStmt(j*), ...)(v_suffix).
  --   Since v_suffix ∈ Δ(fold(oStmt(j*)), f̄), the fold value ≠ f̄(v_suffix).
  -- Inductive step (k > j*): The guard check c_{k*ϑ} = oStmt(k)(v_{k*ϑ}) passes (from h_accept).
  --   Combined with c_{k*ϑ} ≠ f̄^{(k)}(v_{k*ϑ}), we get oStmt(k) ≠ f̄^{(k)} at v_{k*ϑ}.
  --   By ¬E_k (from h_no_bad_global), disagreement propagates through folding.
  --   By compliance (from h_good_after), fold(f̄^{(k)}) = f̄^{(k+1)}.
  --   So fold(oStmt(k))(v_{(k+1)*ϑ}) ≠ f̄^{(k+1)}(v_{(k+1)*ϑ}).
  have h_fold_ne_const :
      logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨ℓ / ϑ - 1, by omega⟩ v stmtIn
        (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v) ≠
      stmtIn.final_constant := by
    -- Base disagreement at block j*: computed fold value differs from decoded next codeword.
    have h_base_ne :
        logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          j_star_idx v stmtIn
          (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            oStmtIn j_star_idx v)
        ≠ f_bar_next v_suffix := by
      have h_eval_eq_fold :
          logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            j_star_idx v stmtIn
            (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              oStmtIn j_star_idx v)
          = folded_f v_suffix := by
        have h_v_suffix_eq :
            getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (k := j_star_idx) (v := v) = v_suffix := by
          rfl
        have h_eval_eq_fold_raw :=
          logical_computeFoldedValue_eq_iterated_fold 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
            (k := j_star_idx)
            (v := v) (stmt := stmtIn)
        have h_eval_eq_fold' := h_eval_eq_fold_raw
        rw [h_v_suffix_eq] at h_eval_eq_fold'
        have h_folded_f_eq :
            folded_f v_suffix =
              iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := ⟨j_star_idx.val * ϑ, by
                  exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (h := k_mul_ϑ_lt_ℓ (k := j_star_idx))⟩)
                (steps := ϑ) (h_destIdx := by rfl)
                (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := j_star_idx))
                (f := oStmtIn ⟨j_star_idx.val, by
                  simpa [nBlocks, toOutCodewordsCount_last, j_star_idx] using h_j_star_lt_div⟩)
                (r_challenges := fun j =>
                  stmtIn.challenges ⟨j_star_idx.val * ϑ + j.val, by
                    have h_le : j_star_idx.val * ϑ + ϑ ≤ ℓ :=
                      k_succ_mul_ϑ_le_ℓ_₂ (k := j_star_idx)
                    have h_lt : j_star_idx.val * ϑ + j.val < j_star_idx.val * ϑ + ϑ := by
                      exact Nat.add_lt_add_left j.isLt (j_star_idx.val * ϑ)
                    exact lt_of_lt_of_le h_lt h_le⟩)
                (y := v_suffix) := by
          unfold folded_f f_star
          rw [h_r_challenges]
          rfl
        calc
          logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              j_star_idx v stmtIn
              (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                oStmtIn j_star_idx v)
              =
            iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨j_star_idx.val * ϑ, by
                exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (h := k_mul_ϑ_lt_ℓ (k := j_star_idx))⟩)
              (steps := ϑ) (h_destIdx := by rfl)
              (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := j_star_idx))
              (f := oStmtIn ⟨j_star_idx.val, by
                simpa [nBlocks, toOutCodewordsCount_last, j_star_idx] using h_j_star_lt_div⟩)
              (r_challenges := fun j =>
                stmtIn.challenges ⟨j_star_idx.val * ϑ + j.val, by
                  have h_le : j_star_idx.val * ϑ + ϑ ≤ ℓ :=
                    k_succ_mul_ϑ_le_ℓ_₂ (k := j_star_idx)
                  have h_lt : j_star_idx.val * ϑ + j.val < j_star_idx.val * ϑ + ϑ := by
                    exact Nat.add_lt_add_left j.isLt (j_star_idx.val * ϑ)
                  exact lt_of_lt_of_le h_lt h_le⟩)
              (y := v_suffix) := h_eval_eq_fold'
          _ = folded_f v_suffix := by
            exact h_folded_f_eq.symm
      have h_disagree_val : folded_f v_suffix ≠ f_bar_next v_suffix := by
        have h_disagree_val := h_disagree
        simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
          at h_disagree_val
        exact h_disagree_val
      intro h_eq
      have h_eq' : folded_f v_suffix = f_bar_next v_suffix := by
        rw [← h_eval_eq_fold]
        exact h_eq
      exact h_disagree_val h_eq'
    by_cases h_more : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
    · -- Main propagation case (j* is not the last block).
      have h_propagates_to_last :
          logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ⟨ℓ / ϑ - 1, by omega⟩ v stmtIn
            (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v) ≠
          stmtIn.final_constant := by
        let j_first : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_star.val + 1, h_more⟩
        have h_f_next_oracle :
            f_next =
              getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
                (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
                  change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
                  exact h_more)
                (destDomainIdx := ⟨j_star.val * ϑ + ϑ, by
                  exact
                    lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                      h_destIdx_le'⟩)
                (h_destDomainIdx := by rfl) := by
          rcases h_f_next_shape with h_shape | h_const
          · exact h_shape.2
          · exact False.elim (h_const.1 h_more)
        let j_first_idx : Fin (ℓ / ϑ) := ⟨j_star.val + 1, by
          have h_lt := h_more
          simp only [nBlocks, toOutCodewordsCount_last] at h_lt
          exact h_lt⟩
        have h_first_guard :
            logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              j_star_idx v stmtIn
              (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                oStmtIn j_star_idx v) =
            (oStmtIn j_first)
              (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (v := v)
                (destIdx := ⟨j_first_idx.val * ϑ, by
                  exact
                    lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                      (h := k_mul_ϑ_lt_ℓ (k := j_first_idx))⟩)
                (h_destIdx_le := Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := j_first_idx)))) := by
          have h_pos : 0 < j_first.val := by
            dsimp [j_first]
            omega
          exact
            logical_checkSingleRepetition_guard_eq (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
              (h_accept := h_accept) (j := j_first) h_pos
        have h_first_point_ne :
            (oStmtIn j_first)
              (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (v := v)
                (destIdx := ⟨j_first_idx.val * ϑ, by
                  exact
                    lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                      (h := k_mul_ϑ_lt_ℓ (k := j_first_idx))⟩)
                (h_destIdx_le := Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := j_first_idx)))) ≠
            f_bar_next v_suffix := by
          intro h_eq
          apply h_base_ne
          exact h_first_guard.trans h_eq
        have h_jfirst_good :
            ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j_first := by
          apply h_good_after
          exact Fin.lt_def.mpr (by
            dsimp [j_first]
            omega)
        let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := j_first
        have h_idx_eq :
            queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (ℓ := ℓ) (ϑ := ϑ) j_star =
            queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next := by
          simpa [j_next, j_first] using
            queryBlockDestIdx_eq_queryBlockSourceIdx_succ
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ)
              (j := j_star) (hj := h_more)
        have h_idx_cast :
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate
              (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (ℓ := ℓ) (ϑ := ϑ) j_star)) =
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate
              (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (ℓ := ℓ) (ϑ := ϑ) j_next)) := by
          exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx_eq
        have h_getNext_eq :
            getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
              (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
                change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
                exact h_more)
              (destDomainIdx := queryBlockDestIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
              (h_destDomainIdx := by rfl) =
            fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y) := by
          simpa [j_next, j_first] using
            getNextOracle_eq_oracleStatement (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (oStmt := oStmtIn) (j := j_star) (hj := h_more)
        have h_f_next_cast_eq :
            f_next =
              fun y => (oStmtIn j_next) (cast h_idx_cast y) := by
          rw [h_f_next_oracle, h_getNext_eq]
        have h_jfirst_close :
            UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (queryBlockSourceIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
              (queryBlockSourceIdx_le
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
              (oStmtIn j_next) :=
          goodBlock_implies_currentUDRClose (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_next) (by
              simpa [j_next] using h_jfirst_good)
        have h_jfirst_close_stmt :
            UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (queryBlockDestIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
              (queryBlockDestIdx_le
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
              (fun y => (oStmtIn j_next) (cast h_idx_cast y)) := by
          rw [← h_f_next_cast_eq]
          exact h_next_close
        have h_first_codeword_eq :
            f_bar_next v_suffix =
              goodBlockCodeword (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_next) (by
                  simpa [j_next] using h_jfirst_good)
                (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
          have h_fbar_eq :
              f_bar_next =
                UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (queryBlockDestIdx
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
                  (queryBlockDestIdx_le
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
                  (f := fun y => (oStmtIn j_next) (cast h_idx_cast y))
                  (h_within_radius := h_jfirst_close_stmt) := by
            cases h_f_next_cast_eq
            exact
              UDRCodeword_eq_of_close (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := queryBlockDestIdx
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
                (h_i := queryBlockDestIdx_le
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
                (f := fun y => (oStmtIn j_next) (cast h_idx_cast y))
                h_next_close h_jfirst_close_stmt
          have h_left := congrFun h_fbar_eq v_suffix
          have h_transport :=
            successor_codeword_eval_eq (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (ℓ := ℓ) (ϑ := ϑ)
              (oStmtIn := oStmtIn) (j := j_star) (hj := h_more) (v := v)
              (h_next_close_stmt := h_jfirst_close_stmt)
              (h_next_close := h_jfirst_close)
          dsimp only [j_next, j_first] at h_transport
          rw [← queryBlockDestSuffix_eq_queryBlockSourceSuffix_succ
            (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (ℓ := ℓ) (ϑ := ϑ) (j := j_star) (hj := h_more) (v := v)] at h_transport
          calc
            f_bar_next v_suffix =
                UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (queryBlockDestIdx
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
                  (queryBlockDestIdx_le
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star)
                  (f := fun y => (oStmtIn j_next) (cast h_idx_cast y))
                  (h_within_radius := h_jfirst_close_stmt)
                  (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_star v) := h_left
            _ =
                UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (queryBlockSourceIdx
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
                  (queryBlockSourceIdx_le
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
                  (f := oStmtIn j_next)
                  (h_within_radius := h_jfirst_close)
                  (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) :=
              h_transport
            _ =
                goodBlockCodeword (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_next) (by
                    simpa [j_next] using h_jfirst_good)
                  (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
              rfl
        have h_first_point_ne_good :
            (oStmtIn j_first)
              (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_first v) ≠
            goodBlockCodeword (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_first) h_jfirst_good
              (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_first v) := by
          intro h_eq
          apply h_first_point_ne
          exact h_eq.trans h_first_codeword_eq.symm
        have h_good_of_ge :
            ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
              j_first.val ≤ j.val →
              ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j := by
          intro j h_ge
          have hlt : j_star < j := Fin.lt_def.mpr (by
            have h_ge' := h_ge
            dsimp [j_first] at h_ge'
            omega)
          exact h_good_after j hlt
        let j_last : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨ℓ / ϑ - 1, by
          have h_lt : ℓ / ϑ - 1 < ℓ / ϑ := Nat.pred_lt (Nat.ne_of_gt h_div_pos)
          simpa [nBlocks, toOutCodewordsCount_last] using h_lt⟩
        have h_jfirst_le_jlast : j_first.val ≤ j_last.val := by
          dsimp [j_first, j_last]
          have h_more' := h_more
          simp only [nBlocks, toOutCodewordsCount_last] at h_more'
          omega
        have h_propagate_aux :
            ∀ d : ℕ, ∀ (h_bound : d ≤ j_last.val - j_first.val),
              let j_cur : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_first.val + d, by
                have h_le : j_first.val + d ≤ j_last.val := by
                  have h_add : d + j_first.val ≤ j_last.val :=
                    (Nat.le_sub_iff_add_le h_jfirst_le_jlast).mp h_bound
                  simpa [Nat.add_comm] using h_add
                exact lt_of_le_of_lt h_le j_last.isLt⟩
              (oStmtIn j_cur)
                (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_cur v) ≠
              goodBlockCodeword (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_cur)
                (h_good_of_ge j_cur (by
                  dsimp [j_cur]
                  omega))
                (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_cur v) := by
          intro d
          induction d with
          | zero =>
              intro h_bound
              dsimp
              exact h_first_point_ne_good
          | succ d ih =>
              intro h_bound
              let j_prev : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_first.val + d, by
                have h_le : j_first.val + d ≤ j_last.val := by
                  have h_add : d + j_first.val ≤ j_last.val :=
                    (Nat.le_sub_iff_add_le h_jfirst_le_jlast).mp (by omega)
                  simpa [Nat.add_comm] using h_add
                exact lt_of_le_of_lt h_le j_last.isLt⟩
              let j_cur : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_first.val + (d + 1), by
                have h_le : j_first.val + (d + 1) ≤ j_last.val := by
                  have h_add : (d + 1) + j_first.val ≤ j_last.val :=
                    (Nat.le_sub_iff_add_le h_jfirst_le_jlast).mp h_bound
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_add
                exact lt_of_le_of_lt h_le j_last.isLt⟩
              have h_prev_ge : j_first.val ≤ j_prev.val := by
                dsimp [j_prev]
                omega
              have h_cur_ge : j_first.val ≤ j_cur.val := by
                dsimp [j_cur]
                omega
              have h_prev_point_ne := ih (by omega)
              have h_prev_succ : j_prev.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
                have h_le : j_prev.val + 1 ≤ j_last.val := by
                  dsimp [j_prev]
                  omega
                exact lt_of_le_of_lt h_le j_last.isLt
              have h_prev_good :
                  ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn
                    j_prev := by
                exact h_good_of_ge j_prev h_prev_ge
              have h_cur_good :
                  ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn
                    j_cur := by
                exact h_good_of_ge j_cur h_cur_ge
              have h_cur_eq : j_cur = ⟨j_prev.val + 1, h_prev_succ⟩ := by
                apply Fin.ext
                dsimp [j_cur, j_prev]
                omega
              have h_step :=
                goodBlock_point_disagreement_step (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (stmtIn := stmtIn) (oStmtIn := oStmtIn)
                  (j := j_prev) (hj := h_prev_succ)
                  (h_good := h_prev_good) (h_next_good := by
                    simpa only [h_cur_eq] using h_cur_good)
                  (h_no_bad_global := h_no_bad_global)
                  (v := v) (h_accept := h_accept)
                  (h_point_ne := by
                    simpa [j_prev] using h_prev_point_ne)
              subst j_cur
              exact h_step
        let j_end : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_first.val + (j_last.val - j_first.val), by
          have h_le : j_first.val + (j_last.val - j_first.val) ≤ j_last.val := by
            rw [Nat.add_sub_of_le h_jfirst_le_jlast]
          exact lt_of_le_of_lt h_le j_last.isLt⟩
        have h_jend_eq_jlast : j_end = j_last := by
          apply Fin.eq_of_val_eq
          dsimp [j_end]
          rw [Nat.add_sub_of_le h_jfirst_le_jlast]
        have h_last_point_ne :
            (oStmtIn j_end)
              (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end v) ≠
            goodBlockCodeword (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_end)
              (h_good_of_ge j_end (by
                dsimp [j_end]
                rw [Nat.add_sub_of_le h_jfirst_le_jlast]
                exact h_jfirst_le_jlast))
              (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end v) := by
          simpa [j_end] using
            h_propagate_aux (j_last.val - j_first.val) (by omega)
        have h_no_last_succ_last :
            ¬ j_last.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
          have h_div_pos' : 1 ≤ ℓ / ϑ := Nat.succ_le_of_lt h_div_pos
          dsimp [j_last]
          simp only [nBlocks, toOutCodewordsCount_last]
          omega
        have h_no_last_succ :
            ¬ j_end.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
          simpa [h_jend_eq_jlast] using h_no_last_succ_last
        have h_jlast_good :
            ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j_end := by
          exact h_good_of_ge j_end (by
            dsimp [j_end]
            rw [Nat.add_sub_of_le h_jfirst_le_jlast]
            exact h_jfirst_le_jlast)
        have h_last_compliant :=
          goodBlock_last_isCompliant (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_end)
            (hj := h_no_last_succ) h_jlast_good
        rcases h_last_compliant with ⟨h_fw_last, h_const_close, h_fold_eq_last⟩
        have h_last_point_ne_raw := h_last_point_ne
        rw [goodBlockCodeword_eq_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn) (j := j_end)
          h_jlast_good h_fw_last] at h_last_point_ne_raw
        have h_mem_fiber_last :
            queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end v ∈
            fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (queryBlockSourceIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
              ϑ (h_destIdx := by rfl)
              (h_destIdx_le := queryBlockDestIdx_le
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
              (oStmtIn j_end)
              (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (queryBlockSourceIdx
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                (queryBlockSourceIdx_le
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                (f := oStmtIn j_end)
                (h_within_radius :=
                  UDRClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (i := queryBlockSourceIdx
                      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                    (steps := ϑ)
                    (h_destIdx := by rfl)
                    (h_destIdx_le := queryBlockDestIdx_le
                      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                    (f := oStmtIn j_end) h_fw_last)) :=
          point_disagreement_mem_fiberwiseDisagreement
            (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (oStmtIn := oStmtIn) (ℓ := ℓ) (ϑ := ϑ) (j := j_end) (v := v)
            (g := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (queryBlockSourceIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
              (queryBlockSourceIdx_le
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
              (f := oStmtIn j_end)
              (h_within_radius :=
                UDRClose_of_fiberwiseClose (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (i := queryBlockSourceIdx
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                  (steps := ϑ)
                  (h_destIdx := by rfl)
                  (h_destIdx_le := queryBlockDestIdx_le
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                  (f := oStmtIn j_end) h_fw_last))
            h_last_point_ne_raw
        have h_no_bad_last :=
          no_foldingBadEvent_of_no_bad_global (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (oStmtIn := oStmtIn) (stmtIn := stmtIn) (j := j_end) h_no_bad_global
        have h_subset_last := h_no_bad_last
        unfold foldingBadEvent at h_subset_last
        simp only [h_fw_last, not_not, ↓reduceDIte] at h_subset_last
        have h_mem_disagree_last := h_subset_last h_mem_fiber_last
        have h_last_idx_eq :
            queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j_end =
            (⟨ℓ / ϑ - 1, by omega⟩ : Fin (ℓ / ϑ)) := by
          apply Fin.eq_of_val_eq
          dsimp [queryBlockIdx, j_end]
          rw [Nat.add_sub_of_le h_jfirst_le_jlast]
        have h_eval_eq_last :=
          logical_computeFoldedValue_eq_iterated_fold (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (oStmt := oStmtIn)
            (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j_end)
            (v := v) (stmt := stmtIn)
        have h_eval_ne_last :
            logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j_end) v stmtIn
              (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                oStmtIn (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j_end) v) ≠
            stmtIn.final_constant := by
          have h_mem_disagree_last' := h_mem_disagree_last
          simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
            at h_mem_disagree_last'
          intro h_eq
          apply h_mem_disagree_last'
          have h_fold_eq_eval :=
            congrFun h_fold_eq_last
              (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end v)
          have h_suffix_eq :
              getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j_end) (v := v) =
              queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end v := by
            rfl
          have h_const_eval :
              UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (queryBlockDestIdx
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                (queryBlockDestIdx_le
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
                (f := fun _ => stmtIn.final_constant)
                (h_within_radius := h_const_close)
                (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end v) =
              stmtIn.final_constant := by
            rw [UDRCodeword_constFunc_eq_self (𝔽q := 𝔽q) (β := β)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := queryBlockDestIdx
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
              (h_i := queryBlockDestIdx_le
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_end)
              (c := stmtIn.final_constant)]
          rw [h_suffix_eq] at h_eval_eq_last
          exact
            h_eval_eq_last.symm.trans
              ((h_eq.trans h_const_eval.symm).trans h_fold_eq_eval.symm)
        rw [h_last_idx_eq] at h_eval_ne_last
        exact h_eval_ne_last
      exact h_propagates_to_last
    · -- Terminal case: j* is the last block, so base disagreement is already
      -- the final-step disagreement.
      have hj_not_lt_succ : ¬ j_star.val + 1 < ℓ / ϑ := by
        have hj_not_lt_succ := h_more
        simp only [nBlocks, toOutCodewordsCount_last] at hj_not_lt_succ
        exact hj_not_lt_succ
      have h_k_last_eq_jstar :
          (⟨ℓ / ϑ - 1, by omega⟩ : Fin (ℓ / ϑ)) =
          j_star_idx := by
        apply Fin.eq_of_val_eq
        have h_ge : ℓ / ϑ ≤ j_star.val + 1 := Nat.le_of_not_gt hj_not_lt_succ
        have h1 : ℓ / ϑ - 1 ≤ j_star.val := by omega
        have h2 : j_star.val ≤ ℓ / ϑ - 1 := by omega
        exact Nat.le_antisymm h1 h2
      have h_f_next_const : f_next = fun _ => stmtIn.final_constant := by
        rcases h_f_next_shape with h_shape | h_const
        · exact False.elim (h_more h_shape.1)
        · exact h_const.2
      have h_f_bar_next_const : f_bar_next = fun _ => stmtIn.final_constant := by
        subst f_next
        dsimp [f_bar_next]
        exact
          UDRCodeword_constFunc_eq_self (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨j_star.val * ϑ + ϑ, by
              exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx_le'⟩)
            (h_i := h_destIdx_le) (c := stmtIn.final_constant)
      have h_base_ne_const :
          logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            j_star_idx v stmtIn
            (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              oStmtIn j_star_idx v)
          ≠ stmtIn.final_constant := by
        intro h_eq_const
        have h_eq' : logical_computeFoldedValue 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_star_idx v stmtIn
            (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              oStmtIn j_star_idx v) = f_bar_next v_suffix := by
          rw [h_f_bar_next_const]
          exact h_eq_const
        exact h_base_ne h_eq'
      rw [← h_k_last_eq_jstar] at h_base_ne_const
      exact h_base_ne_const
  -- Step 3: Contradiction.
  exact h_fold_ne_const h_final

end QueryPhaseSoundnessStatements

end

end Binius.BinaryBasefold
