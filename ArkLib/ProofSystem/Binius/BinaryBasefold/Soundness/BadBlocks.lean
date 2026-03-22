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

/-- Number of oracle blocks at the end of the protocol. -/
abbrev nBlocks : ℕ := toOutCodewordsCount ℓ ϑ (Fin.last ℓ)

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

/-- Congruence lemma for `UDRClose`: transport along a `Fin r` equality.
Given two `Fin r` indices with the same value and `HEq` functions, `UDRClose` transfers. -/
lemma UDRClose_of_fin_eq {i j : Fin r} (hij : i = j)
    {hi : ↑i ≤ ℓ} {hj : ↑j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g) (h : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hi f) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j hj g := by
  subst hij; exact eq_of_heq hfg ▸ h

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
    (D : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) :
    Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∈ D
    ] = (D.card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := by
  classical
  -- Setup
  let S0 := sDomain 𝔽q β h_ℓ_add_R_rate 0
  let Sdest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let steps : ℕ := destIdx.val
  have h_destIdx : destIdx.val = (0 : Fin r).val + steps := by simp [steps]
  let suffix : S0 → Sdest :=
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := destIdx) (h_destIdx_le := h_destIdx_le)
  -- Express probability via cardinalities
  rw [prob_uniform_eq_card_filter_div_card]
  -- Define the preimage set
  let preimage : Finset S0 := Finset.univ.filter (fun v => suffix v ∈ D)
  -- Each fiber over y has size 2^steps
  let fiberSet : Sdest → Finset S0 := fun y =>
    (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
      h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))).toFinset
  have h_fiber_card : ∀ y : Sdest, (fiberSet y).card = 2 ^ steps := by
    intro y
    have h :=
      card_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (y := y)
    -- Convert Fintype.card of the set to Finset.card
    have h_card :
        (fiberSet y).card =
          Fintype.card
            (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))) := by
      classical
      dsimp [fiberSet]
      exact
        Set.toFinset_card
          (s := Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps))))
    calc
      (fiberSet y).card =
          Fintype.card
            (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))) := h_card
      _ = 2 ^ steps := h
  -- Preimage equals union of fibers over D
  have h_preimage_eq :
      preimage = D.biUnion fiberSet := by
    ext v
    constructor
    · intro hv
      have hv' : suffix v ∈ D := by
        simp only [preimage] at hv ⊢
        exact (Finset.mem_filter.mp hv).2
      -- v is in the fiber of its suffix
      have hv_fiber : v ∈ fiberSet (suffix v) := by
        -- Use the fiber index corresponding to v
        let k :=
          pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (steps := steps) h_destIdx h_destIdx_le (x := v)
        have hk :
            qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := suffix v) k = v := by
          -- suffix v is exactly the iterated quotient of v
          have h_eq :
              suffix v =
                iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
                  (destIdx := destIdx) (k := steps) (h_destIdx := h_destIdx)
                  (h_destIdx_le := h_destIdx_le) (x := v) := by
            simp [suffix, extractSuffixFromChallenge, steps]
          -- Use the characterization of fibers
          exact (is_fiber_iff_generates_quotient_point 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
            (h_destIdx_le := h_destIdx_le) (x := v) (y := suffix v)).1 h_eq
        -- Show membership in the fiber set
        have : v ∈ Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := suffix v)) (Set.univ : Set (Fin (2 ^ steps))) := by
          refine ⟨k, by simp, hk⟩
        change
          v ∈ (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
            h_destIdx h_destIdx_le (y := suffix v)) (Set.univ : Set (Fin (2 ^ steps)))).toFinset
        rw [Set.mem_toFinset]
        exact this
      -- Put together
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨suffix v, hv', hv_fiber⟩
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨y, hyD, hv_fiber⟩
      -- From v ∈ fiberSet y, deduce suffix v = y
      have hv_fiber' :
          v ∈ Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps))) := by
        change
          v ∈ (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))).toFinset at hv_fiber
        rw [Set.mem_toFinset] at hv_fiber
        exact hv_fiber
      rcases hv_fiber' with ⟨k, hk_mem, hk_eq⟩
      have h_eq :
          y =
            iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
              (destIdx := destIdx) (k := steps) (h_destIdx := h_destIdx)
              (h_destIdx_le := h_destIdx_le) (x := v) := by
        -- v is in the fiber of y, so y is the iterated quotient of v
        apply generates_quotient_point_if_is_fiber_of_y 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (x := v) (y := y)
        refine ⟨k, ?_⟩
        exact hk_eq.symm
      have : suffix v = y := by
        -- Rewrite suffix v as iteratedQuotientMap
        dsimp [suffix, extractSuffixFromChallenge, steps]
        exact h_eq.symm
      -- Conclude v ∈ preimage
      apply Finset.mem_filter.mpr
      constructor
      · simp only [mem_univ]
      · -- suffix v ∈ D
        rw [this]
        exact hyD
  -- Cardinality of the preimage
  have h_preimage_card : preimage.card = D.card * 2 ^ steps := by
    -- Use disjoint union of fibers
    have h_disjoint :
        ∀ y₁ ∈ D, ∀ y₂ ∈ D, y₁ ≠ y₂ →
          Disjoint (fiberSet y₁) (fiberSet y₂) := by
      intro y₁ hy₁ y₂ hy₂ hy_ne
      -- Apply fiber disjointness lemma
      have h :=
        qMap_total_fiber_disjoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
          (h_destIdx_le := h_destIdx_le) (y₁ := y₁) (y₂ := y₂) hy_ne
      simp only [fiberSet] at h ⊢
      exact h
    -- Now compute the card via biUnion
    calc
      preimage.card
          = (D.biUnion fiberSet).card := by simp only [h_preimage_eq]
      _ = ∑ y ∈ D, (fiberSet y).card := by
          exact Finset.card_biUnion (s := D) (t := fiberSet) (h := h_disjoint)
      _ = ∑ y ∈ D, 2 ^ steps := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp only [h_fiber_card]
      _ = D.card * 2 ^ steps := by
          simp only [sum_const, smul_eq_mul]
  -- Cardinality of the source domain
  have h_card_S0 : Fintype.card S0 = Fintype.card Sdest * 2 ^ steps := by
    -- Use sDomain_card and the fact |𝔽q| = 2
    have h0 :
        Fintype.card S0 = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - (0 : Fin r)) := by
      change Fintype.card ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) =
        (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - (0 : Fin r))
      exact sDomain_card 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
        (h_i := Sdomain_bound (by omega))
    have hdest :
        Fintype.card Sdest = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - destIdx) := by
      change Fintype.card ↥(sDomain 𝔽q β h_ℓ_add_R_rate destIdx) =
        (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - destIdx)
      exact sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx)
        (h_i := Sdomain_bound (by omega))
    -- Rewrite and use pow_add
    have h_add : (ℓ + 𝓡) = (ℓ + 𝓡 - destIdx.val) + destIdx.val := by
      have h_le : destIdx.val ≤ ℓ + 𝓡 := by omega
      exact (Nat.sub_add_cancel h_le).symm
    -- Convert to the desired form
    -- We use hF₂.out to rewrite |𝔽q| = 2
    have hFq : Fintype.card 𝔽q = 2 := hF₂.out
    calc
      Fintype.card S0
          = (Fintype.card 𝔽q) ^ (ℓ + 𝓡) := by
              rw [h0]
              simp
      _ = (Fintype.card 𝔽q) ^ ((ℓ + 𝓡 - destIdx.val) + destIdx.val) := by
        exact congrArg (HPow.hPow (Fintype.card 𝔽q)) h_add
      _ = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - destIdx.val) *
          (Fintype.card 𝔽q) ^ destIdx.val := by
              simp [pow_add]
      _ = Fintype.card Sdest * 2 ^ steps := by
              -- rewrite with hdest and |𝔽q| = 2
          simp only [hFq, hdest, steps]
  -- Finish the probability computation
  have h_card_pos : (((2 ^ steps : ℕ) : ENNReal)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero steps (by decide : (2 : ℕ) ≠ 0))
  have h_card_fin : (((2 ^ steps : ℕ) : ENNReal)) ≠ ⊤ := by
    simp
  -- Rewrite in terms of cards
  have h_prob :
      (preimage.card : ENNReal) / Fintype.card S0
        = (D.card : ENNReal) / Fintype.card Sdest := by
    calc
      (preimage.card : ENNReal) / Fintype.card S0
          = ((D.card * 2 ^ steps : ℕ) : ENNReal) /
              (Fintype.card Sdest * 2 ^ steps : ℕ) := by
            simp [h_preimage_card, h_card_S0, preimage, S0, Sdest]
      _ = (D.card : ENNReal) / Fintype.card Sdest := by
            -- Cancel the factor 2^steps
            -- (a*b)/(c*b) = a/c
            rw [Nat.cast_mul, Nat.cast_mul]
            rw [mul_comm (D.card : ENNReal) (((2 ^ steps : ℕ) : ENNReal))]
            rw [mul_comm (Fintype.card Sdest : ENNReal) (((2 ^ steps : ℕ) : ENNReal))]
            exact
              ENNReal.mul_div_mul_left (a := (D.card : ENNReal))
                (b := (Fintype.card Sdest : ENNReal))
                (c := (((2 ^ steps : ℕ) : ENNReal)))
                h_card_pos h_card_fin
  dsimp [preimage] at h_prob ⊢
  exact h_prob


end QueryPhaseSoundnessStatements

end

end Binius.BinaryBasefold
