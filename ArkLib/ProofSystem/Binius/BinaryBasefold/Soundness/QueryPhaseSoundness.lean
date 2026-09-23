/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module


public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryRejection

/-!
# Binary Basefold query-phase probability bound

Proposition 4.24 of [DP24], using the terminal suffix rejection lemmas in `QueryRejection`.
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

omit [CharP L 2] [SampleableType L] in
open Classical in
/-- **Proposition 4.24** (Query-phase soundness, assuming no bad events).

If any oracle is non-compliant and no bad folding event occurs, then a single
repetition of the proximity check accepts with probability at most
`(1/2) + 1/(2 * 2^𝓡)`. -/
theorem prop_4_24_singleRepetition_proximityCheck_bound
    {h_le : ϑ ≤ ℓ}
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_consistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := h_le) (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr{ let v ←$ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant
    ] ≤ ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡)) := by
  classical
  -- Extract a concrete bad block from `h_not_consistent`.
  have h_exists_badBlock :
      ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
        badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn) j := by
    -- Define final-step compliance as in `badBlockProp`'s last branch.
    let j_last := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k := j_last.val * ϑ
    have h_k : k = ℓ - ϑ := by
      dsimp [j_last, k]
      simp only [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.div_mul_cancel (hdiv.out),
        one_mul]
    have hk_add : k + ϑ = ℓ := by
      rw [h_k]
      exact Nat.sub_add_cancel (by omega)
    let final_compliance : Prop :=
      isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k); omega⟩)
        (steps := ϑ) (destIdx := ⟨k + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ); omega⟩)
        (h_destIdx := by rfl) (h_destIdx_le := by simp only [hk_add, le_refl])
        (f_i := oStmtIn j_last)
        (f_i_plus_steps := fun _ => stmtIn.final_constant)
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := k) (h := by simp only [hk_add, Fin.val_last, le_refl]))
    have h_not_and :
        ¬ (oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := Fin.last ℓ) (challenges := stmtIn.challenges) (oStmt := oStmtIn) ∧
            final_compliance) := by
      have h_not_and := h_not_consistent
      simp only [not_and, finalSumcheckStepOracleConsistencyProp, Fin.val_last] at h_not_and ⊢
      exact h_not_and
    by_cases h_final_ok : final_compliance
    · -- Final block compliant: then oracleFoldingConsistencyProp must fail.
      have h_oracle_bad :
          ¬ oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := Fin.last ℓ) (challenges := stmtIn.challenges) (oStmt := oStmtIn) := by
        intro h_oracle_ok
        exact h_not_and ⟨h_oracle_ok, h_final_ok⟩
      have h_oracle_bad' :
          ∃ (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
            (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)),
            ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨j.val * ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact (Nat.le_add_right _ _).trans
                  (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j))
              ⟩)
              (steps := ϑ)
              (destIdx := ⟨j.val * ϑ + ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j)
              ⟩)
              (h_destIdx := by rfl)
              (h_destIdx_le := by
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j))
              (f_i := oStmtIn j)
              (f_i_plus_steps :=
                getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
                  (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
                    change j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
                    exact hj)
                  (destDomainIdx := ⟨j.val * ϑ + ϑ, by
                    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j)⟩)
                  (h_destDomainIdx := by rfl))
              (challenges :=
                getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                  stmtIn.challenges (k := j.val * ϑ) (h := by
                    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j))) := by
        -- Unfold oracleFoldingConsistencyProp and push the negation inside.
        have h_not_forall :
            ¬ (∀ (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
                (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)),
              isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := ⟨j.val * ϑ, by
                  apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  exact (Nat.le_add_right _ _).trans
                    (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j))
                ⟩)
                (steps := ϑ)
                (destIdx := ⟨j.val * ϑ + ϑ, by
                  apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j)
                ⟩)
                (h_destIdx := by rfl)
                (h_destIdx_le := by
                  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j))
                (f_i := oStmtIn j)
                (f_i_plus_steps :=
                  getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
                    (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
                      change j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
                      exact hj)
                    (destDomainIdx := ⟨j.val * ϑ + ϑ, by
                      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                        (i := Fin.last ℓ) (j := j)⟩)
                    (h_destDomainIdx := by rfl))
                (challenges :=
                  getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                    stmtIn.challenges (k := j.val * ϑ) (h := by
                      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                        (i := Fin.last ℓ) (j := j)))) := by
          have h_not_forall := h_oracle_bad
          simp only [oracleFoldingConsistencyProp] at h_not_forall
          exact h_not_forall
        classical
        push Not at h_not_forall
        exact h_not_forall
      rcases h_oracle_bad' with ⟨j, hj, hbad⟩
      refine ⟨j, ?_⟩
      have hj' : j.val + 1 < ℓ / ϑ := by
        have hj' := hj
        simp only [nBlocks, toOutCodewordsCount_last] at hj'
        exact hj'
      have hbad' := hbad
      simp only [badBlockProp, hj', nBlocks, toOutCodewordsCount_last] at hbad' ⊢
      exact hbad'
    · -- Final block non-compliant: take the last block.
      refine ⟨j_last, ?_⟩
      have h_no_succ :
          ¬ j_last.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
        have h_div_pos : 0 < ℓ / ϑ :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
        have h_div_pos' : 1 ≤ ℓ / ϑ := Nat.succ_le_iff.mpr h_div_pos
        have h_eq : j_last.val + 1 = nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
          simp [j_last, nBlocks, getLastOraclePositionIndex_last,
            toOutCodewordsCount_last, Nat.sub_add_cancel h_div_pos']
        exact not_lt_of_ge (by simp only [toOutCodewordsCount_last, h_eq, le_refl])
      have h_no_succ' : ¬ j_last.val + 1 < ℓ / ϑ := by
        have h_no_succ' := h_no_succ
        simp only [nBlocks, toOutCodewordsCount_last] at h_no_succ'
        exact h_no_succ'
      have h_final_ok' := h_final_ok
      simp only [badBlockProp, h_no_succ', final_compliance, nBlocks, toOutCodewordsCount_last]
        at h_final_ok' ⊢
      exact h_final_ok'
  -- Pick the highest bad block.
  let j_star :=
    highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists_badBlock
  have h_j_star_bad :
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j_star := by
    exact
      highestBadBlock_is_bad 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists_badBlock
  have h_good_of_lt {j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))} (hlt : j_star < j) :
      ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn) j :=
    not_badBlock_of_lt_highest 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists_badBlock hlt
  -- Indices for the chosen bad block.
  set i_star : Fin ℓ := ⟨j_star.val * ϑ, by
    simp only [(oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))]⟩
  set destIdx : Fin r := ⟨j_star.val * ϑ + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    simp only [(oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))]⟩
  have h_destIdx : destIdx.val = i_star.val + ϑ := by
    simp [i_star, destIdx]
  have h_destIdx_le : destIdx ≤ ℓ := by
    change j_star.val * ϑ + ϑ ≤ ℓ
    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star)
  let f_star := oStmtIn j_star
  let r_challenges : Fin ϑ → L :=
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
      stmtIn.challenges (k := j_star.val * ϑ)
      (h := by
        exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))
  -- No bad event at the chosen block.
  have h_no_bad_event :
      ¬ foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) ϑ (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_i := f_star) (r_challenges := r_challenges) := by
    intro h_bad
    apply h_no_bad
    refine ⟨j_star, ?_⟩
    have h_branch :
        (oraclePositionToDomainIndex (positionIdx := j_star)).val + ϑ ≤ (Fin.last ℓ).val := by
      simp only [Fin.val_last,
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))]
    have h_bad' := h_bad
    unfold foldingBadEventAtBlock
    set_option backward.isDefEq.respectTransparency false in
      simp only [h_branch, r_challenges, i_star, destIdx] at h_bad' ⊢
    exact h_bad'
  -- Choose `f_next` and extract compliance/UDR-close facts.
  have h_choose :
      ∃ f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx,
        (¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i_star, by omega⟩) ϑ (destIdx := destIdx)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges)) ∧
        UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          destIdx h_destIdx_le f_next ∧
        ((∃ hj : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ),
          f_next =
            getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
              (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
                change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
                exact hj)
              (destDomainIdx := destIdx) (h_destDomainIdx := by
                exact h_destIdx))
        ∨ (¬ j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) ∧
            f_next = fun _ => stmtIn.final_constant)) := by
    by_cases h_last : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
    · -- Intermediate bad block.
      let f_next :
          OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
        getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
            change j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
            exact h_last)
          (destDomainIdx := destIdx) (h_destDomainIdx := by rfl)
      have h_not_compliant :
          ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i_star, by omega⟩) ϑ (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
            (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges) := by
        have h_last' : j_star.val + 1 < ℓ / ϑ := by
          have h_last' := h_last
          simp only [nBlocks, toOutCodewordsCount_last] at h_last'
          exact h_last'
        have h_j_star_bad' := h_j_star_bad
        simp only [badBlockProp, h_last', nBlocks, toOutCodewordsCount_last]
          at h_j_star_bad'
        exact h_j_star_bad'
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_star.val + 1, h_last⟩
      have h_next_good :
          ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (stmtIn := stmtIn) (oStmtIn := oStmtIn) j_next := by
        have hlt : j_star < j_next := by
          exact Fin.lt_def.mpr (by simp [j_next])
        exact h_good_of_lt (j := j_next) hlt
      have h_next_close :
          UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            destIdx h_destIdx_le f_next := by
        have h_j_next_mul_lt_r : ↑j_next * ϑ < r := by
          have : ↑j_next * ϑ = destIdx.val := by simp only [j_next, destIdx]; ring
          omega
        have h_idx : (⟨↑j_next * ϑ, h_j_next_mul_lt_r⟩ : Fin r) = destIdx := by
          apply Fin.ext; simp only [j_next, destIdx]; ring
        have h_udr := goodBlock_implies_UDRClose 𝔽q β stmtIn oStmtIn j_next h_next_good
          (h_idx := h_idx) (h_le := h_destIdx_le)
        exact h_udr
      exact ⟨f_next, h_not_compliant, h_next_close, Or.inl ⟨h_last, rfl⟩⟩
    · -- Final bad block: `f_next` is the constant oracle.
      let f_next :
          OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
        fun _ => stmtIn.final_constant
      have h_not_compliant :
          ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i_star, by omega⟩) ϑ (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
            (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges) := by
        -- Reduce `badBlockProp` to its final-block branch, then rewrite `j_last` to `j_star`.
        have h_j_star_last : j_star = getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) := by
          apply Fin.ext
          have h_val : j_star.val = (nBlocks (ℓ := ℓ) (ϑ := ϑ)) - 1 := by
            have h_lt : j_star.val < (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := j_star.isLt
            have h_ge : (nBlocks (ℓ := ℓ) (ϑ := ϑ)) ≤ j_star.val + 1 := by
              exact Nat.le_of_not_gt h_last
            omega
          simp [getLastOraclePositionIndex, nBlocks, h_val]
        have h_no_succ' : ¬ j_star.val + 1 < ℓ / ϑ := by
          simp only [nBlocks, toOutCodewordsCount_last] at h_last
          exact h_last
        let j_last : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) :=
          getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
        have h_j_star_bad' :
            ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨j_last.val * ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact (Nat.le_add_right _ _).trans
                  (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j_last))⟩)
              (steps := ϑ)
              (destIdx := ⟨j_last.val * ϑ + ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j_last)⟩)
              (h_destIdx := by rfl)
              (h_destIdx_le := by
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j_last))
              (f_i := oStmtIn j_last)
              (f_i_plus_steps := fun _ => stmtIn.final_constant)
              (challenges :=
                getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                  stmtIn.challenges
                  (k := j_last.val * ϑ) (h := by
                    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j_last))) := by
          simp only [badBlockProp, h_no_succ', nBlocks, toOutCodewordsCount_last] at h_j_star_bad
          exact h_j_star_bad
        have h_j_last_to_star : j_last = j_star := by
          simp only [j_last] at h_j_star_last ⊢
          exact h_j_star_last.symm
        have h_j_star_bad'' : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨j_star.val * ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              exact (Nat.le_add_right _ _).trans
                (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j_star))⟩)
            (steps := ϑ)
            (destIdx := ⟨j_star.val * ϑ + ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := j_star)⟩)
            (h_destIdx := by rfl)
            (h_destIdx_le := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := j_star))
            (f_i := oStmtIn j_star)
            (f_i_plus_steps := fun _ => stmtIn.final_constant)
            (challenges :=
              getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                stmtIn.challenges (k := j_star.val * ϑ) (h := by
                  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j_star))) := by
          have h := h_j_star_bad'
          rw [h_j_last_to_star] at h
          exact h
        simp only [i_star, destIdx, f_star, f_next, r_challenges] at h_j_star_bad'' ⊢
        exact h_j_star_bad''
      have h_next_close :
          UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            destIdx h_destIdx_le f_next := by
        exact
          (constFunc_UDRClose (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
            (h_i := h_destIdx_le) (c := stmtIn.final_constant))
      exact ⟨f_next, h_not_compliant, h_next_close, Or.inr ⟨h_last, rfl⟩⟩
  rcases h_choose with ⟨f_next, h_not_compliant, h_next_close, h_f_next_shape⟩
  -- Apply Lemma 4.25: folded function is far from the decoded next codeword.
  have h_not_pair :
      let f_i_star_folded :=
        iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨i_star, by omega⟩ ϑ h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
      let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
      ¬ pair_UDRClose 𝔽q β destIdx h_destIdx_le f_i_star_folded f_bar_next := by
    exact
      lemma_4_25_dist_folded_ge_of_last_noncompliant (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i_star := i_star) (steps := ϑ)
        (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_star := f_star) (f_next := f_next) (r_challenges := r_challenges)
        h_not_compliant h_no_bad_event h_next_close
  -- Disagreement set between folded oracle and decoded next codeword.
  let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i_star, by omega⟩ ϑ h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
  let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
  let D :=
    disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
      (f := folded_f) (g := f_bar_next)
  -- From `¬ pair_UDRClose`, derive a lower bound on |D|.
  have h_dist_ge :
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≤
        2 * D.card := by
    have h' :
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≤
          2 * Δ₀(folded_f, f_bar_next) := by
      have h'' := not_lt.mp h_not_pair
        -- f_bar_next = UDRCodeword ... = Classical.choose ..., so types should match
      exact h''
    simp only [D, disagreementSet, hammingDist] at h' ⊢
    exact h'
  -- Acceptance implies the suffix is NOT in the disagreement set.
  have h_accept_subset :
      ∀ v : sDomain 𝔽q β h_ℓ_add_R_rate 0,
        logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn v stmtIn stmtIn.final_constant →
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D := by
    intro v h_accept h_mem
    have h_reject :=
      lemma_4_26_reject_if_suffix_in_disagreement (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
        (j_star := j_star) (destIdx := destIdx) (h_destIdx := by simp [destIdx])
        (h_destIdx_le := h_destIdx_le) (f_next := f_next)
        (r_challenges := r_challenges) (h_r_challenges := by rfl)
        (h_f_next_shape := h_f_next_shape)
        (h_no_bad_event := by
          simp only [i_star, destIdx] at h_no_bad_event; exact h_no_bad_event)
        (h_next_close := h_next_close)
        (h_good_after := fun j hlt => h_good_of_lt hlt)
        (h_no_bad_global := h_no_bad) (v := v)
    exact h_reject (by
      simp only [UDRCodeword, SetLike.mem_coe, uniqueDecodingRadius_eq_floor_div_2, and_imp, D,
        folded_f, f_bar_next] at h_mem ⊢
      exact h_mem) h_accept
  -- Probability bound via monotonicity.
  have h_prob_accept_le :
      Pr{ let v ←$ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn v stmtIn stmtIn.final_constant
      ] ≤
      Pr{ let v ←$ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D
      ] := by
    exact prEvent_mono ($ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0)) _ _ h_accept_subset
  -- Evaluate the suffix probability for the complement set.
  have h_prob_suffix_not :
      Pr{ let v ←$ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D
      ] =
      ((Dᶜ).card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := by
    have h :=
      prob_uniform_suffix_mem (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) (D := Dᶜ)
    simp only [Finset.mem_compl, D] at h ⊢
    exact h
  -- Bound the complement probability using the distance bound.
  have h_prob_bound :
      ((Dᶜ).card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
        ≤ ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡)) := by
    -- Set up notation.
    let Sdest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let n : ℕ := Fintype.card Sdest
    have h_card_Sdest :
        n = 2 ^ (ℓ + 𝓡 - destIdx.val) := by
      have h := (sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx)
          (h_i := Sdomain_bound (by omega)))
      simp only [n, hF₂.out] at h ⊢
      exact h
    have h_exp :
        ℓ + 𝓡 - destIdx.val = 𝓡 + (ℓ - destIdx.val) := by
      have h_le : destIdx.val ≤ ℓ := by exact h_destIdx_le
      calc
        ℓ + 𝓡 - destIdx.val = 𝓡 + ℓ - destIdx.val := by omega
        _ = 𝓡 + (ℓ - destIdx.val) := by
          exact Nat.add_sub_assoc h_destIdx_le 𝓡
    have h_n_div :
        n / 2 ^ 𝓡 = 2 ^ (ℓ - destIdx.val) := by
      have h_pos : 0 < 2 ^ 𝓡 := by
        exact pow_pos (by decide : 0 < (2 : ℕ)) _
      calc
        n / 2 ^ 𝓡
            = (2 ^ (ℓ + 𝓡 - destIdx.val)) / 2 ^ 𝓡 := by simp [h_card_Sdest]
        _ = (2 ^ (𝓡 + (ℓ - destIdx.val))) / 2 ^ 𝓡 := by
              simp [h_exp]
        _ = (2 ^ 𝓡 * 2 ^ (ℓ - destIdx.val)) / 2 ^ 𝓡 := by
              simp only [pow_add, ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
                not_false_eq_true, mul_div_cancel_left₀]
        _ = 2 ^ (ℓ - destIdx.val) := by
          have h := Nat.mul_div_left (2 ^ (ℓ - destIdx.val)) h_pos
          simp only [Nat.mul_comm] at h ⊢
          exact h
    have h_d_next :
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx =
          n - n / 2 ^ 𝓡 + 1 := by
      have h_d :=
        BBF_CodeDistance_eq (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)
      rw [h_n_div, h_card_Sdest]
      exact h_d
    have h_Dcomp_nat :
        2 * (Dᶜ).card ≤ n + n / 2 ^ 𝓡 := by
      have h_card_compl :
          (Dᶜ).card = n - D.card := by
        have h := Finset.card_compl (s := D)
        simp only [Sdest, n] at h ⊢
        exact h
      have h1 :
          2 * (Dᶜ).card = 2 * n - 2 * D.card := by
        simp only [h_card_compl, Nat.mul_sub_left_distrib]
      have h2 :
          2 * n - 2 * D.card ≤ 2 * n -
            BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
        exact Nat.sub_le_sub_left h_dist_ge _
      have h3 :
          2 * n -
            BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≤
            n + n / 2 ^ 𝓡 := by
        simp [h_d_next]; omega
      exact le_trans (by
      simp only [h1] at h2 ⊢
      exact h2) h3
    have h_n_pos : (n : ENNReal) ≠ 0 := by
      -- exact_mod_cast (pow_ne_zero (ℓ + 𝓡 - destIdx.val) (by decide : (2 : ℕ) ≠ 0))
      simp [h_card_Sdest]
    have h_n_fin : (n : ENNReal) ≠ ⊤ := by simp
    have h_Dcomp_ennreal :
        (2 * (Dᶜ).card : ENNReal) ≤
          (n : ENNReal) + ((n / 2 ^ 𝓡 : ℕ) : ENNReal) := by
      exact_mod_cast h_Dcomp_nat
    have h_div_cast :
        ((n / 2 ^ 𝓡 : ℕ) : ENNReal) =
          (n : ENNReal) / (2 ^ 𝓡 : ENNReal) := by
      have h_dvd : (2 ^ 𝓡) ∣ n := by
        refine ⟨2 ^ (ℓ - destIdx.val), ?_⟩
        calc
          n = 2 ^ (ℓ + 𝓡 - destIdx.val) := h_card_Sdest
          _ = 2 ^ (𝓡 + (ℓ - destIdx.val)) := by simp [h_exp]
          _ = 2 ^ 𝓡 * 2 ^ (ℓ - destIdx.val) := by
            simp only [pow_add]
      have h_pos : (2 ^ 𝓡 : ENNReal) ≠ 0 := by
        exact_mod_cast (pow_ne_zero 𝓡 (by decide : (2 : ℕ) ≠ 0))
      have h_pos_nn : (2 ^ 𝓡 : NNReal) ≠ 0 := by
        exact_mod_cast (pow_ne_zero 𝓡 (by decide : (2 : ℕ) ≠ 0))
      have h_div_nn : ((n / 2 ^ 𝓡 : ℕ) : NNReal) = (n : NNReal) / (2 ^ 𝓡 : NNReal) := by
        have h := Nat.cast_div (K := NNReal) h_dvd (by
          simp only [cast_pow, cast_ofNat, ne_eq, h_pos_nn, not_false_eq_true])
        simp only [cast_pow, cast_ofNat] at h
        exact h
      have h_div_cast := congr_arg (ENNReal.ofNNReal) h_div_nn
      simp only [ENNReal.coe_div h_pos_nn] at h_div_cast
      exact h_div_cast
    have h_Dcomp_ennreal' :
        (2 * (Dᶜ).card : ENNReal) ≤
          (n : ENNReal) + (n : ENNReal) / (2 ^ 𝓡 : ENNReal) := by
      have h_Dcomp_ennreal' := h_Dcomp_ennreal
      rw [h_div_cast] at h_Dcomp_ennreal'
      exact h_Dcomp_ennreal'
    have h_step :
        ((Dᶜ).card : ENNReal) ≤
          ((2 : ENNReal)⁻¹ * ((n : ENNReal) + (n : ENNReal) / (2 ^ 𝓡 : ENNReal))) := by
      rw [← ENNReal.mul_le_iff_le_inv (by simp) (by simp)]
      exact h_Dcomp_ennreal'
    apply (ENNReal.div_le_iff h_n_pos h_n_fin).2
    have h_rhs :
        ((2 : ENNReal)⁻¹ * ((n : ENNReal) + (n : ENNReal) / (2 ^ 𝓡 : ENNReal))) =
          ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2 ^ 𝓡)) * (n : ENNReal) := by
      have h_inv : (2 * 2 ^ 𝓡 : ENNReal)⁻¹ = 2⁻¹ * (2 ^ 𝓡 : ENNReal)⁻¹ := by
        apply ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))
      simp [mul_add, add_mul, h_inv, div_eq_mul_inv, mul_assoc, mul_comm]
    have h_step' := h_step
    rw [h_rhs] at h_step'
    exact h_step'
  have h_prob_suffix_not' :
      Pr{ let v ←$ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D
      ] ≤ ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡)) := by
    rw [h_prob_suffix_not]
    exact h_prob_bound
  exact le_trans h_prob_accept_le h_prob_suffix_not'

end QueryPhaseSoundnessStatements

end

end Binius.BinaryBasefold
