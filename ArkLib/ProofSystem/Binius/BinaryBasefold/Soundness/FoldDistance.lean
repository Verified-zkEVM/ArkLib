/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance

/-!
# Binary Basefold: folded distance at a noncompliant oracle

## Main statements

* `iteratedFold_eq_of_eq_on_fiber`: two oracles that agree on the fiber of `y` have equal folds
  at `y`.
* `disagreementSet_iteratedFold_subset_fiberwiseDisagreementSet`: folding creates no
  disagreement outside the fiberwise disagreement set, for any two oracles and any challenges
  (the containment of [DP24] Lemma 4.19, there stated for an oracle and its decoded codeword).
* `not_pairUniqueDecodingClose_iteratedFold_of_not_isCompliant`: at a noncompliant oracle whose next
  oracle is within the unique-decoding radius, and outside the folding bad event, the fold is
  not within the unique-decoding radius of the next oracle's decoded codeword ([DP24]
  Lemma 4.25). The query-phase soundness consumes it.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

omit [Fintype 𝔽q] in
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

open Classical in
omit [DecidableEq 𝔽q] hF₂ [NeZero ℓ] [SampleableType L] in
/-- If `f` and `g` agree on the fiber of `y`, their folds agree at `y`. -/
lemma iteratedFold_eq_of_eq_on_fiber (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    (h_fiber_agree : ∀ x,
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
        (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y →
      f x = g x) :
    (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      h_destIdx h_destIdx_le f (r_challenges := r_challenges) y =
    (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      h_destIdx h_destIdx_le g (r_challenges := r_challenges) (y := y))) := by
  -- Expand to matrix form: fold(y) = Tensor(r) * M_y * fiber_vals
  rw [iteratedFold_eq_matrix_form 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
    (r_challenges := r_challenges)]
  rw [iteratedFold_eq_matrix_form 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
    (r_challenges := r_challenges)]
  -- iteratedFoldMatrixForm 𝔽q β i steps h_destIdx h_destIdx_le g r y
  unfold iteratedFoldMatrixForm pointFoldMatrixForm
  simp only
  congr 2
  let fiberValsF := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f y
  let fiberValsG := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g y
  have h_fiber_eval_eq : fiberValsF = fiberValsG := by
    unfold fiberValsF fiberValsG fiberEvaluations
    ext idx
    let x := quotientFiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y idx
    have h_x_folds_to_y := eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β
      (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (x := x) (y := y) (hx_is_fiber := by use idx)
    exact h_fiber_agree x h_x_folds_to_y.symm
  unfold fiberValsF fiberValsG at h_fiber_eval_eq
  rw [h_fiber_eval_eq]

omit [DecidableEq 𝔽q] hF₂ [NeZero ℓ] [SampleableType L] in
/-- The disagreement set of the folds of `f` and `g` is contained in their fiberwise
disagreement set. -/
lemma disagreementSet_iteratedFold_subset_fiberwiseDisagreementSet (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    let folded_f := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges)
    let folded_g := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges)
    disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
      (f := folded_f) (g := folded_g) ⊆
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
    apply h_not_in_fiber_diff
    refine ⟨x, by simp only [SetLike.coe_mem], ?_⟩
    simp only [Subtype.coe_eta]
    exact ⟨hx, h_neq⟩
  have h_fold_eq := iteratedFold_eq_of_eq_on_fiber 𝔽q β i steps
    h_destIdx h_destIdx_le f g (r_challenges := r_challenges) (y := y) h_agree_on_fiber
  exact hy_mem h_fold_eq

omit [DecidableEq 𝔽q] [NeZero ℓ] [SampleableType L] in
/-- If the oracle `f_star` is not compliant with the next oracle `f_next`, the folding bad event
does not occur at `f_star`, and `f_next` is within the unique-decoding radius, then the fold of
`f_star` is not within the unique-decoding radius of the decoded codeword of `f_next`. -/
lemma not_pairUniqueDecodingClose_iteratedFold_of_not_isCompliant (i_star : Fin ℓ) (steps : ℕ)
    [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i_star.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin steps → L)
    (h_not_compliant : ¬ IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le
       f_star f_next (challenges := r_challenges))
    (h_no_bad_event : ¬ FoldingBadEvent 𝔽q β (i := ⟨i_star, by omega⟩)
      steps h_destIdx h_destIdx_le f_star r_challenges)
    (h_next_close : UniqueDecodingClose 𝔽q β destIdx f_next) :
      let f_i_star_folded := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star r_challenges
    let f_bar_next := uniqueDecodingCodeword 𝔽q β destIdx h_destIdx_le
      (f := f_next) (h_within_radius := h_next_close)
    ¬ PairUniqueDecodingClose 𝔽q β destIdx f_i_star_folded f_bar_next := by
  -- Definitions for clarity
  let d_next := codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C_next := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let f_bar_next := uniqueDecodingCodeword 𝔽q β destIdx h_destIdx_le
      (f := f_next) (h_within_radius := h_next_close)
  let f_i_star_folded := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star r_challenges
  have h_f_bar_next_mem_C_next : f_bar_next ∈ C_next := by -- due to definition
    unfold f_bar_next uniqueDecodingCodeword
    apply uniqueDecodingCodeword_mem_code (i := destIdx) (h_i := h_destIdx_le)
      (f := f_next) (h_within_radius := h_next_close)
  have h_d_next_ne_0 : d_next ≠ 0 :=
    Nat.ne_of_gt (codeDistance_pos 𝔽q β destIdx)
  let d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩)
    steps h_destIdx h_destIdx_le (f := f_star)
  -- Split into Case 1 (Close) and Case 2 (Far)
  by_cases h_fw_close : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_star)
  -- Case 1: Fiberwise Close (d < d_next / 2)
  · have h_fw_dist_lt := h_fw_close -- This gives 2 * fiber_dist < d_next
    -- Choose the unique fiberwise-close codeword for f_star.
    obtain ⟨f_bar_star, ⟨h_f_bar_star_mem, h_f_bar_star_min_card,
        h_f_bar_star_eq_UDRCodeword⟩, -⟩ :=
      exists_unique_codeword_of_fiberwiseClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩)
        (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f := f_star) (h_fw_close := h_fw_close)
    have h_fw_dist_f_g_eq :
        #(fiberwiseDisagreementSet 𝔽q β ⟨i_star, by omega⟩ steps
          h_destIdx h_destIdx_le f_star f_bar_star) = d_fw := by
      unfold d_fw
      rw [h_f_bar_star_min_card]; rfl
    let folded_f_bar_star := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i_star, by omega⟩
       steps h_destIdx h_destIdx_le f_bar_star (r_challenges := r_challenges)
    have h_folded_f_bar_star_mem_C_next : folded_f_bar_star ∈ C_next := by
      unfold folded_f_bar_star
      apply iteratedFold_mem_code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := ⟨f_bar_star, h_f_bar_star_mem⟩)
        (r_challenges := r_challenges)
    -- We prove two inequalities (1) and (2) as per the proof sketch.
    -- Distinct codewords differ by at least the code distance.
    -- First, show that `folded_f_bar_star` ≠ `f_bar_next`.
    -- This follows because `f_star` is NON-COMPLIANT.
    have h_codewords_neq : f_bar_next ≠ folded_f_bar_star := by
      by_contra h_eq
      -- If they were equal, `IsCompliant` would be true (satisfying all 3 conditions).
      apply h_not_compliant
      use h_fw_dist_lt -- Condition 1: f_star is close
      use h_next_close -- Condition 2: f_next is close
      -- Condition 3: folded decoding equals next decoding
      simp only
      rw [←h_f_bar_star_eq_UDRCodeword]
      -- The decoded source folds to the decoded next oracle.
      exact id (Eq.symm h_eq)
    -- Since they are distinct codewords, their distance is at least `d_next`.
    have h_ineq_1 : Δ₀(f_bar_next, folded_f_bar_star) ≥ d_next := by
      apply Code.pairDist_ge_code_mindist_of_ne (C := (C_next : Set _))
        (u := f_bar_next) (v := folded_f_bar_star)
      · exact h_f_bar_next_mem_C_next
      · exact h_folded_f_bar_star_mem_C_next
      · exact h_codewords_neq
    -- Bound the distance between the folded functions.
    -- We know |Δ_fiber(f*, f_bar*)| < d_next / 2 (from fiberwise close hypothesis).
    have h_fiber_dist_lt_half :
        2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i_star, by omega⟩) steps
          h_destIdx h_destIdx_le f_star f_bar_star).card < d_next := by
      rw [Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      -- Express the fiber-disagreement bound using the integer half-distance radius.
      rw [h_fw_dist_f_g_eq]
      rw [←Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      unfold d_fw
      unfold FiberwiseClose at h_fw_close
      norm_cast at h_fw_close
    -- Folding containment: d(fold(f), fold(g)) ≤ |Δ_fiber(f, g)|
    have h_ineq_2 : 2 * Δ₀(f_i_star_folded, folded_f_bar_star) < d_next := by
      calc
        2 * Δ₀(iteratedFold 𝔽q β ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le
          f_star (r_challenges := r_challenges), folded_f_bar_star)
        _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i_star, by omega⟩) steps
            h_destIdx h_destIdx_le f_star f_bar_star).card := by
          -- Hamming distance is card(disagreementSet)
          -- disagreementSet ⊆ fiberwiseDisagreementSet
          apply Nat.mul_le_mul_left
          have res := disagreementSet_iteratedFold_subset_fiberwiseDisagreementSet 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star) (steps := steps)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
            (f := f_star) (g := f_bar_star) (r_challenges := r_challenges)
          simp only at res
          apply Finset.card_le_card
          exact res
        _ < d_next := h_fiber_dist_lt_half
    -- Apply the reverse triangle inequality.
    -- d(A, C) ≥ d(B, C) - d(A, B)
    -- We want 2 * d(f_i_star_folded, f_bar_next) ≥ d_next
    have h_triangle :
        Δ₀(f_bar_next, folded_f_bar_star) ≤
          Δ₀(f_bar_next, f_i_star_folded) + Δ₀(f_i_star_folded, folded_f_bar_star) :=
      hammingDist_triangle f_bar_next f_i_star_folded folded_f_bar_star
    have h_final_bound :
        2 * d_next ≤
          2 * Δ₀(f_bar_next, f_i_star_folded) + 2 * Δ₀(f_i_star_folded, folded_f_bar_star) := by
      have h_trans : d_next ≤ Δ₀(f_bar_next, folded_f_bar_star) := h_ineq_1
      have h_mul : 2 * d_next ≤ 2 * Δ₀(f_bar_next, folded_f_bar_star) :=
        Nat.mul_le_mul_left 2 h_trans
      linarith [h_triangle, h_mul]
    -- We have 2*d_next ≤ 2*d(Target) + (something < d_next)
    -- This implies 2*d(Target) > d_next
    -- Or in integer arithmetic: 2*d(Target) ≥ d_next
    rw [hammingDist_comm] at h_final_bound -- align directions
    unfold PairUniqueDecodingClose
    simp only [not_lt, ge_iff_le]
    apply le_of_not_gt
    intro h_contra
    -- If 2 * d(target) < d_next:
    -- Sum < d_next + d_next = 2*d_next. Contradiction.
    linarith [h_ineq_2, h_final_bound, h_contra]
  -- Fiberwise distance is at least half the code distance.
  · -- In this case, the definition of `FoldingBadEvent` (Case 2 branch) simplifies.
    -- The bad event is defined as: UniqueDecodingClose(f_next).
    unfold FoldingBadEvent at h_no_bad_event
    simp only [h_fw_close, ↓reduceDIte] at h_no_bad_event
    -- h_no_bad_event : ¬ UniqueDecodingClose ...
    -- This means f_next is NOT close to the code C_next.
    -- Definition of not UniqueDecodingClose: 2 * dist(f_next, C_next) ≥ d_next
    unfold UniqueDecodingClose at h_no_bad_event
    simp only [not_lt] at h_no_bad_event
    -- ↑(codeDistance 𝔽q β destIdx)
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
    unfold PairUniqueDecodingClose
    simp only [not_lt, ge_iff_le]
    norm_cast at h_no_bad_event_alt

end

end Binius.BinaryBasefold
