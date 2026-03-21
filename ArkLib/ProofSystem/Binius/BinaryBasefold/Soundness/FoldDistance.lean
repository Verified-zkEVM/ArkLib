/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
## Binary Basefold Soundness Fold Distance

Distance and disagreement transfer lemmas from fiber views to folded codewords.
This file packages:
1. helper lemmas turning fiber agreement into fold agreement
2. disagreement propagation from noncompliant fibers to folded evaluations
3. the folded-distance lower bounds used in the later bad-block analysis

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

open Classical in
omit [CharP L 2] [DecidableEq 𝔽q] hF₂ in
/-- Helper: If `f` and `g` agree on the fiber of `y`, their folds agree at `y`.
NOTE: this might not be needed -/
lemma fold_agreement_of_fiber_agreement (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    (∀ x,
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
        (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y →
      f x = g x) →
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges) y =
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges) (y := y))) := by
  intro h_fiber_agree
  -- Expand to matrix form: fold(y) = Tensor(r) * M_y * fiber_vals
  rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  -- ⊢ localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le f r y =
  -- localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le g r y
  unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  simp only
  congr 2
  let left := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f y
  let right := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g y
  have h_fiber_eval_eq : left = right := by
    unfold left right fiberEvaluations
    ext idx
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y idx
    have h_x_folds_to_y := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x) (y := y) (hx_is_fiber := by use idx)
    exact h_fiber_agree x h_x_folds_to_y.symm
  unfold left right at h_fiber_eval_eq
  rw [h_fiber_eval_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ in
/-- Helper: The disagreement set of the folded functions is a subset of the fiberwise disagreement set. -/
lemma disagreement_fold_subset_fiberwiseDisagreement (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges)
    let folded_g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges)
    disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl) (f := folded_f) (g := folded_g) ⊆
    fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f g := by
  simp only
  intro y hy_mem
  simp only [disagreementSet, ne_eq, mem_filter, mem_univ, true_and] at hy_mem
  simp only [fiberwiseDisagreementSet, ne_eq, Subtype.exists, mem_filter, mem_univ, true_and]
  -- Contrapositive: If y is NOT in fiberwise disagreement, then f and g agree on fiber.
  -- Then folds must agree (lemma above). Then y is NOT in disagreement set.
  by_contra h_not_in_fiber_diff
  have h_agree_on_fiber : ∀ x,
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
        (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y →
      f x = g x := by
    intro x hx
    by_contra h_neq
    exact h_not_in_fiber_diff ⟨x, (by simp only [SetLike.coe_mem]), (by simp only [Subtype.coe_eta]; constructor; exact hx; exact h_neq)⟩
  have h_fold_eq := fold_agreement_of_fiber_agreement 𝔽q β i steps h_destIdx h_destIdx_le f g (r_challenges := r_challenges) (y := y) h_agree_on_fiber
  exact hy_mem h_fold_eq

/-- **Lemma 4.24**
For `i*` where `f^(i)` is non-compliant, `f^(i+ϑ)` is UDR-close, and the bad event `E_{i*}`
doesn't occur, the folded function of `f^(i)` is not UDR-close to the UDR-decoded codeword
of `f^(i+ϑ)`. -/
lemma lemma_4_24_dist_folded_ge_of_last_noncompliant (i_star : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i_star.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin steps → L)
    -- 1. f_next is the actual folded function
    -- 2. i* is non-compliant
    (h_not_compliant : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le
       f_star f_next (challenges := r_challenges))
    -- 3. No bad event occurred at i*
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star r_challenges)
    -- 4. The next function `f_next` IS close enough to have a unique codeword `f_bar_next`
    (h_next_close : UDRClose 𝔽q β destIdx h_destIdx_le f_next) :
      let f_i_star_folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star r_challenges
    -- **CONCLUSION**: 2 * d(f_next, f_bar_next) ≥ d_{i* + steps}
    let f_bar_next := UDRCodeword 𝔽q β destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
    ¬ pair_UDRClose 𝔽q β destIdx h_destIdx_le f_i_star_folded f_bar_next := by
  -- Definitions for clarity
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C_cur := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let f_bar_next := UDRCodeword 𝔽q β destIdx h_destIdx_le
      (f := f_next) (h_within_radius := h_next_close)
  let f_i_star_folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star r_challenges
  have h_f_bar_next_mem_C_next : f_bar_next ∈ C_next := by -- due to definition
    unfold f_bar_next UDRCodeword
    apply UDRCodeword_mem_BBF_Code (i := destIdx) (h_i := h_destIdx_le) (f := f_next) (h_within_radius := h_next_close)
  have h_d_next_ne_0 : d_next ≠ 0 := by
    unfold d_next
    simp [BBF_CodeDistance_eq (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le)]
  let d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩)
    steps h_destIdx h_destIdx_le (f := f_star)
  -- Split into Case 1 (Close) and Case 2 (Far)
  by_cases h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star)
  -- Case 1: Fiberwise Close (d < d_next / 2)
  · let h_fw_dist_lt := h_fw_close -- This gives 2 * fiber_dist < d_next
    -- Define f_bar_star (the unique decoded codeword for f_star) to be the **fiberwise**-close codeword to f_star
    obtain ⟨f_bar_star, ⟨h_f_bar_star_mem, h_f_bar_star_min_card, h_f_bar_star_eq_UDRCodeword⟩, h_unique⟩ := exists_unique_fiberwiseClosestCodeword_within_UDR 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star) (h_fw_close := h_fw_close)
    have h_fw_dist_f_g_eq : #(fiberwiseDisagreementSet 𝔽q β ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star f_bar_star) = d_fw := by
      unfold d_fw
      rw [h_f_bar_star_min_card]; rfl
    let folded_f_bar_star := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩
       steps h_destIdx h_destIdx_le f_bar_star (r_challenges := r_challenges)
    have h_folded_f_bar_star_mem_C_next : folded_f_bar_star ∈ C_next := by
      unfold folded_f_bar_star
      apply iterated_fold_preserves_BBF_Code_membership 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := ⟨f_bar_star, h_f_bar_star_mem⟩) (r_challenges := r_challenges)
    -- We prove two inequalities (1) and (2) as per the proof sketch.
    -- **Step (1): Distance between the two codewords in C_next**
    -- First, show that `folded_f_bar_star` ≠ `f_bar_next`.
    -- This follows because `f_star` is NON-COMPLIANT.
    have h_codewords_neq : f_bar_next ≠ folded_f_bar_star := by
      by_contra h_eq
      -- If they were equal, `isCompliant` would be true (satisfying all 3 conditions).
      apply h_not_compliant
      use h_fw_dist_lt -- Condition 1: f_star is close
      use h_next_close -- Condition 2: f_next is close
      -- Condition 3: folded decoding equals next decoding
      simp only
      rw [←h_f_bar_star_eq_UDRCodeword]
      -- ⊢ iterated_fold ⟨i*, ⋯⟩ steps ⋯ f_bar_star r_challenges = UDRCodeword 𝔽q β ⟨i* + steps, ⋯⟩ f_next h_next_close
      exact id (Eq.symm h_eq)
    -- Since they are distinct codewords, their distance is at least `d_next`.
    have h_ineq_1 : Δ₀(f_bar_next, folded_f_bar_star) ≥ d_next := by
      apply Code.pairDist_ge_code_mindist_of_ne (C := (C_next : Set _))
        (u := f_bar_next) (v := folded_f_bar_star)
      · exact h_f_bar_next_mem_C_next
      · exact h_folded_f_bar_star_mem_C_next
      · exact h_codewords_neq
    -- **Step (2): Distance between folded functions**
    -- We know |Δ_fiber(f*, f_bar*)| < d_next / 2 (from fiberwise close hypothesis).
    have h_fiber_dist_lt_half :
        2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star f_bar_star).card < d_next := by
      rw [Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      -- ⊢ #(fiberwiseDisagreementSet 𝔽q β i_star steps h_destIdx h_destIdx_le f_star f_bar_star) ≤ (d_next - 1) / 2
      rw [h_fw_dist_f_g_eq]
      rw [←Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      unfold d_fw
      unfold fiberwiseClose at h_fw_close
      norm_cast at h_fw_close
    -- Lemma 4.18 (Geometric): d(fold(f), fold(g)) ≤ |Δ_fiber(f, g)|
    have h_ineq_2 : 2 * Δ₀(f_i_star_folded, folded_f_bar_star) < d_next := by
      calc
        2 * Δ₀(iterated_fold 𝔽q β ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star (r_challenges := r_challenges), folded_f_bar_star)
        _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star f_bar_star).card := by
          -- Hamming distance is card(disagreementSet)
          -- disagreementSet ⊆ fiberwiseDisagreementSet (Lemma 4.18 Helper)
          apply Nat.mul_le_mul_left
          let res := disagreement_fold_subset_fiberwiseDisagreement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star) (g := f_bar_star) (r_challenges := r_challenges)
          simp only at res
          apply Finset.card_le_card
          exact res
        _ < d_next := h_fiber_dist_lt_half
    -- **Final Step: Reverse Triangle Inequality**
    -- d(A, C) ≥ d(B, C) - d(A, B)
    -- We want 2 * d(f_next, f_bar_next) ≥ d_next
    have h_triangle : Δ₀(f_bar_next, folded_f_bar_star) ≤ Δ₀(f_bar_next, f_i_star_folded) + Δ₀(f_i_star_folded, folded_f_bar_star) :=
      hammingDist_triangle f_bar_next f_i_star_folded folded_f_bar_star
    have h_final_bound : 2 * d_next ≤ 2 * Δ₀(f_bar_next, f_i_star_folded) + 2 * Δ₀(f_i_star_folded, folded_f_bar_star) := by
      have h_trans : d_next ≤ Δ₀(f_bar_next, folded_f_bar_star) := h_ineq_1
      have h_mul : 2 * d_next ≤ 2 * Δ₀(f_bar_next, folded_f_bar_star) := Nat.mul_le_mul_left 2 h_trans
      linarith [h_triangle, h_mul]
    -- We have 2*d_next ≤ 2*d(Target) + (something < d_next)
    -- This implies 2*d(Target) > d_next
    -- Or in integer arithmetic: 2*d(Target) ≥ d_next
    rw [hammingDist_comm] at h_final_bound -- align directions
    unfold pair_UDRClose
    simp only [not_lt, ge_iff_le]
    apply le_of_not_gt
    intro h_contra
    -- If 2 * d(target) < d_next:
    -- Sum < d_next + d_next = 2*d_next. Contradiction.
    linarith [h_ineq_2, h_final_bound, h_contra]
  -- **Case 2: Fiberwise Far (d ≥ d_next / 2)**
  · -- In this case, the definition of `foldingBadEvent` (Case 2 branch) simplifies.
    -- The bad event is defined as: UDRClose(f_next).
    unfold foldingBadEvent at h_no_bad_event
    simp only [h_fw_close, ↓reduceDIte] at h_no_bad_event
    -- h_no_bad_event : ¬ UDRClose ...
    -- This means f_next is NOT close to the code C_next.
    -- Definition of not UDRClose: 2 * dist(f_next, C_next) ≥ d_next
    unfold UDRClose at h_no_bad_event
    simp only [not_lt] at h_no_bad_event
    -- ↑(BBF_CodeDistance 𝔽q β destIdx)
    have h_no_bad_event_alt : (d_next : ℕ∞) ≤ 2 * Δ₀(f_i_star_folded, f_bar_next):= by
      calc
        d_next ≤ 2 * Δ₀(f_i_star_folded, (C_next : Set (S_next → L))) := by
          exact h_no_bad_event
        _ ≤ 2 * Δ₀(f_i_star_folded, f_bar_next) := by
          rw [ENat.mul_le_mul_left_iff]
          · simp only [Code.distFromCode_le_dist_to_mem (C := (C_next : Set (S_next → L))) (u :=
              f_i_star_folded) (v := f_bar_next) (hv := h_f_bar_next_mem_C_next)]
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
          · simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true]
    unfold pair_UDRClose
    simp only [not_lt, ge_iff_le]
    norm_cast at h_no_bad_event_alt

end

end Binius.BinaryBasefold
