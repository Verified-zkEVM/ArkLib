/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
import ArkLib.Data.Probability.Instances

/-!
## Binary Basefold Soundness Bad Blocks

Bad-block bookkeeping for the terminal query-phase analysis of Binary Basefold soundness.
This file packages:
1. the bad-block predicate and the corresponding finite bad-block set
2. highest-bad-block and good-block consequences used to localize disagreement
3. the uniform-suffix probability helper used in the final query-phase bound

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering below follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

set_option maxHeartbeats 400000

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
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

variable [hdiv : Fact (ϑ ∣ ℓ)]
variable [SampleableType L]
open QueryPhase

/-- A block index is *bad* if the corresponding folding-compliance check fails. -/
def badBlockProp
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) :
    Fin (nBlocks (ϑ := ϑ) (ℓ := ℓ)) → Prop := fun j =>
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  if hj : j.val + 1 < nBlocks then
    let curDomainIdx : Fin r := ⟨j.val * ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := j.val * ϑ)
      have h := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
      exact (Nat.le_add_right _ _).trans h⟩
    let destIdx : Fin r := ⟨j.val * ϑ + ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := j.val * ϑ + ϑ)
      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)⟩
    ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := curDomainIdx) (steps := ϑ) (destIdx := destIdx)
        (h_destIdx := by rfl) (h_destIdx_le := by
          exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))
        (f_i := oStmtIn j)
        (f_i_plus_steps :=
          getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
              simp only [nBlocks] at hj ⊢
              exact hj) (destDomainIdx := destIdx) (h_destDomainIdx := by rfl))
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := j.val * ϑ) (h := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)))
  else
    let j_last := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k := j_last.val * ϑ
    have h_k : k = ℓ - ϑ := by
      dsimp [j_last, k]
      simp only [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.div_mul_cancel (hdiv.out),
        one_mul]
    have hk_add : k + ϑ = ℓ := by
      simp only [h_k] at h_k ⊢
      exact Nat.sub_add_cancel (by omega)
    have hk_le : k ≤ ℓ := by omega
    ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k); omega
          ⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ); omega
          ⟩)
        (h_destIdx := by rfl)
        (h_destIdx_le := by
          -- k + ϑ = ℓ, so the bound holds
          simp only [hk_add, le_refl])
        (f_i := oStmtIn j_last)
        (f_i_plus_steps := fun _ => stmtIn.final_constant)
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := k) (h := by
              simp only [hk_add, Fin.val_last, le_refl]))

open Classical in
/-- Finset of bad blocks. -/
def badBlockSet
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) :
    Finset (Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :=
  Finset.filter (badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn)) Finset.univ

open Classical in
noncomputable def highestBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j) :
    Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) :=
  (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn)).max' (by
      rcases h_exists with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      exact (Finset.mem_filter.mpr ⟨by simp, hj⟩))

lemma highestBadBlock_is_bad
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j) :
    badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists) := by
  classical
  have hmem :
      highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists
        ∈ badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (stmtIn := stmtIn) (oStmtIn := oStmtIn) := by
    -- max' is always a member of the set
    dsimp [highestBadBlock]
    exact
      Finset.max'_mem
        (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn))
        (by
          rcases h_exists with ⟨j, hj⟩
          refine ⟨j, ?_⟩
          exact (Finset.mem_filter.mpr ⟨by simp, hj⟩))
  have hmem' := Finset.mem_filter.mp hmem
  exact hmem'.2

lemma not_badBlock_of_lt_highest
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j)
    {j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))}
    (hlt : highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists < j) :
    ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j := by
  classical
  intro hj_bad
  have hj_mem :
      j ∈ badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) := by
    exact (Finset.mem_filter.mpr ⟨by simp, hj_bad⟩)
  have h_nonempty :
      (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn)).Nonempty := by
    rcases h_exists with ⟨j', hj'⟩
    refine ⟨j', ?_⟩
    exact (Finset.mem_filter.mpr ⟨by simp, hj'⟩)
  have hle : j ≤ highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists :=
    by
      -- le_max' takes the membership proof; Nonempty is inferred from max'
      dsimp [highestBadBlock]
      exact
        Finset.le_max' (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn)) j hj_mem
  exact not_lt_of_ge hle hlt

/-- If block `j` is not bad (i.e. it is compliant), then the oracle `oStmtIn j` is UDR-close
at its domain position `j.val * ϑ`. This extracts `fiberwiseClose` from `isCompliant`
(the negation of `badBlockProp`) and converts it to `UDRClose` via `UDRClose_of_fiberwiseClose`. -/
lemma goodBlock_implies_UDRClose
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    {destIdx : Fin r}
    (h_idx : (⟨j.val * ϑ, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((Nat.le_add_right _ _).trans
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
          (i := Fin.last ℓ) (j := j)))⟩ : Fin r) = destIdx)
    (h_le : destIdx.val ≤ ℓ) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      destIdx h_le (fun y => (oStmtIn j) (cast (by rw [h_idx]) y)) := by
  subst h_idx; simp only [cast_eq]
  -- Unfold badBlockProp: it's `¬isCompliant` in both branches.
  simp only [badBlockProp] at h_good
  by_cases h_last : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
  · -- Intermediate block: badBlockProp = ¬isCompliant
    simp only [h_last, ↓reduceDIte, not_not] at h_good
    obtain ⟨h_fw, _, _⟩ := h_good
    exact UDRClose_of_fiberwiseClose 𝔽q β _ ϑ (by rfl)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))
      (oStmtIn j) h_fw
  · -- Final block: need getLastOraclePositionIndex = j
    simp only [h_last, ↓reduceDIte, not_not] at h_good
    have h_j_eq : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = j := by
      apply Fin.ext
      simp only [getLastOraclePositionIndex, toOutCodewordsCount_last]
      have h_ge : nBlocks (ℓ := ℓ) (ϑ := ϑ) ≤ j.val + 1 := Nat.le_of_not_gt h_last
      simp only [nBlocks, toOutCodewordsCount_last] at h_ge
      have h_lt : j.val < nBlocks (ℓ := ℓ) (ϑ := ϑ) := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      omega
    subst h_j_eq
    obtain ⟨h_fw, _, _⟩ := h_good
    exact UDRClose_of_fiberwiseClose 𝔽q β _ ϑ (by rfl)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)))
      (oStmtIn (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ))) h_fw

open Classical in
lemma prob_uniform_suffix_mem
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ)
    (D : Finset (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)) :
    Pr_{ let v ←$ᵖ (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) }[
      extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∈ D
    ] = (D.card : ENNReal) /
        Fintype.card (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  sorry


end QueryPhaseSoundnessStatements

end

end Binius.BinaryBasefold
