/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
## Binary Basefold Compliance

Protocol-level proximity, compliance, and bad-event definitions for Binary Basefold.
This file packages:
1. the compliance predicate relating adjacent folded codewords
2. fold-error containment and its UDR-close consequence
3. the full and incremental bad-event predicates used by the soundness development
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Code ReedSolomon BerlekampWelch ProbabilityTheory

noncomputable section SoundnessTools

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}

/--
Compliance condition (Definition 4.17) : For an index `i` that is a multiple of `steps`,
the oracle `f_i` is compliant if it's close to the code fiber-wise, the next oracle
`f_i_plus_steps` is close to its code, and their unique closest codewords are consistent
with folding.
-/
def isCompliant (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
  (challenges : Fin steps → L) : Prop :=
  ∃ (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (f := f_i))
    (h_dist_next_lt : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := by omega) (f := f_i_plus_steps)),
    let h_dist_curr_lt := UDRClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_destIdx h_destIdx_le f_i
      (h_fw_dist_lt := h_fw_dist_lt)
    let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := by omega) (f := f_i) (h_within_radius := h_dist_curr_lt)
    let f_bar_i_plus_steps := UDRCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := by omega)
      f_i_plus_steps h_dist_next_lt
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
      h_destIdx h_destIdx_le
      f_bar_i challenges = f_bar_i_plus_steps

omit [CharP L 2] in
/--
Farness implies non-compliance. If `f_i` is far from its code `C_i`, it cannot be
compliant. This follows directly from the contrapositive of
`fiberwise_dist_lt_imp_dist_lt`.
-/
lemma farness_implies_non_compliance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
  (challenges : Fin steps → L)
  (h_far : 2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    ≥ (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) : ℕ∞)) :
  ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f_i := f_i) (f_i_plus_steps := f_i_plus_steps) (challenges := challenges) := by
  intro h_compliant
  rcases h_compliant with ⟨h_fw_dist_lt, _, _⟩
  have h_close := UDRClose_of_fiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (destIdx := destIdx)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
    (h_fw_dist_lt := h_fw_dist_lt)
  have h_not_far := LT.lt.not_ge h_close
  exact h_not_far h_far

/-- **Fold error containment**: Two words achieve `fold error containment` for a specific
tuple of challenges if folding them does not introduce new errors outside of their
fiberwise disagreement set. -/
def fold_error_containment (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f f_bar : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (r_challenges : Fin steps → L) :=
    let fiberwise_Δ_set := fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f) (g := f_bar)
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := i) h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)
    let folded_f_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := steps) (i := i) h_destIdx h_destIdx_le (f := f_bar)
      (r_challenges := r_challenges)
    let folded_Δ_set := disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl) (f := folded_f)
      (g := folded_f_bar)
    folded_Δ_set ⊆ fiberwise_Δ_set

/-! **Lemma 4.18.** For each `i ∈ {0, steps, ..., ℓ-steps}`, if `f⁽ⁱ⁾` is `UDR-close`, then, for
each tuple of folding challenges `(rᵢ', ..., r_{i+steps-1}') ∈ L^steps`, we have that
`fold error containment` holds.
-- * **Main Idea of Proof:** Proceeds by contraposition. If `y ∉ Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾)`, then the
  restrictions of `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` to the fiber over `y` are identical. By Definition 4.8, this
  implies their folded values at `y` are also identical.
-- * **Intuition**: Because folding is local (Def 4.8), if `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` agree completely on
  the fiber above a point `y`, their folded values at `y` must also agree.
-- * **Consequence**: If `f⁽ⁱ⁾` is close to `f̄⁽ⁱ⁾`, then `fold(f⁽ⁱ⁾)` must be close to
  `fold(f̄⁽ⁱ⁾)`.
-/
omit [CharP L 2] [DecidableEq 𝔽q] in
lemma fold_error_containment_of_UDRClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (challenges : Fin steps → L)
  (h_UDRClose : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)
    (f := f_i)) :
  let f_bar := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)
    (f := f_i) (h_within_radius := h_UDRClose)
  fold_error_containment 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f_i) (f_bar := f_bar) (r_challenges := challenges) := by
  unfold fold_error_containment disagreementSet fiberwiseDisagreementSet
  set f_bar := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)
    (f := f_i) (h_within_radius := h_UDRClose)
  simp only
  intro y hy_in_folded_disagreement
  simp only [ne_eq, mem_filter, mem_univ, true_and] at hy_in_folded_disagreement
  by_contra h_not_in_fiber_disagreement
  simp only [ne_eq, Subtype.exists, mem_filter, mem_univ, true_and, not_exists, not_and,
    Decidable.not_not] at h_not_in_fiber_disagreement
  let folded_f_y := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := i) h_destIdx h_destIdx_le
      (f := f_i) (r_challenges := challenges) (y := y)
  let folded_f_bar_y := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := i) h_destIdx h_destIdx_le
      (f := f_bar) (r_challenges := challenges) (y := y)
  have h_matrix_f := iterated_fold_eq_matrix_form 𝔽q β (i := i) (steps := steps)
    h_destIdx h_destIdx_le (f := f_i) (r_challenges := challenges)
  have h_matrix_f_bar := iterated_fold_eq_matrix_form 𝔽q β (i := i) (steps := steps)
    h_destIdx h_destIdx_le (f := f_bar) (r_challenges := challenges)
  rw [h_matrix_f] at hy_in_folded_disagreement
  rw [h_matrix_f_bar] at hy_in_folded_disagreement
  set fiberEvals_f_i := fiberEvaluations 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le
    (f := f_i) y
  set fiberEvals_f_bar_i := fiberEvaluations 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le
    (f := f_bar) y
  have h_fiber_evals_eq : fiberEvals_f_i = fiberEvals_f_bar_i := by
    ext k
    unfold fiberEvals_f_i fiberEvals_f_bar_i fiberEvaluations
    let x := qMap_total_fiber 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le y k
    apply h_not_in_fiber_disagreement x
    let res := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (x := x) (y := y) (hx_is_fiber := by use k)
    exact res.symm
  have h_folded_eq : localized_fold_matrix_form 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (f := f_i) (r_challenges := challenges) y =
    localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le
      (f := f_bar) (r_challenges := challenges) y := by
    unfold localized_fold_matrix_form
    simp only
    unfold fiberEvals_f_i fiberEvals_f_bar_i at h_fiber_evals_eq
    rw [h_fiber_evals_eq]
  exact hy_in_folded_disagreement h_folded_eq

open Classical in
/-- **Definition 4.19** Bad event for folding : This event captures two scenarios where the
random folding challenges undermine the protocol's soundness checks.
For `i ∈ {0, ..., ℓ - steps}`,
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ₊steps / 2` (fiberwise close):
  `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾, rᵢ', ..., r_{i+steps-1}'), fold(f̄⁽ⁱ⁾, rᵢ', ..., r_{i+steps-1}'))`,
  i.e. fiberwiseDisagreementSet ⊄ foldedDisagreementSet
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ dᵢ₊steps / 2`  (fiberwise far):
  `d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`, i.e. foldedUDRClose
-/
def foldingBadEvent (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (r_challenges : Fin steps → L) : Prop :=
  let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
    (r_challenges := r_challenges)
  if h_is_close : (fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_destIdx h_destIdx_le (f := f_i)) then
    let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx
        h_destIdx_le f_i h_is_close)
    let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_bar_i) (r_challenges := r_challenges)
    ¬ (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le (f := f_i) (g := f_bar_i) ⊆
       disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
         (f := folded_f_i) (g := folded_f_bar_i))
  else
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
      (h_i := by omega) (f := folded_f_i)

open Classical in
/-- **Definition 4.19.2** (Incremental Bad Events).
For block start index `block_start_idx`, block size `ϑ`, and **partial step count**
`k ≤ ϑ`, with `destIdx = block_start_idx + ϑ` (the block destination), `E(block_start_idx, k)` is defined as follows:

- If `k = 0`: Returns `False` (no challenges consumed yet).
- Case 1 (fiberwise close at block level):
  `Δ⁽ⁱ⁾(f, f̄) ⊄ Δ⁽ⁱ⁺ᵏ⁾(fold_k(f), fold_k(f̄))`
  where both sides are projected to `S^{i+ϑ}` (the block destination).
- Case 2 (fiberwise far at block level):
  `d⁽ⁱ⁺ᵏ⁾(fold_k(f), C⁽ⁱ⁺ᵏ⁾) < d_{i+ϑ}/2`
  where `d⁽ⁱ⁺ᵏ⁾` is the fiberwise distance projected to `S^{i+ϑ}`.

When `k = ϑ`, this coincides with `foldingBadEvent`. -/
def incrementalFoldingBadEvent
    (block_start_idx : Fin r) {midIdx destIdx : Fin r} (k : ℕ)
    (h_k_le : k ≤ ϑ) (h_midIdx : midIdx = block_start_idx + k)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_challenges : Fin k → L) : Prop :=
  have h_ik_le : block_start_idx.val + k ≤ ℓ := by omega
  have h_midIdx_to_block : destIdx = midIdx + (ϑ - k) := by omega

  let folded_f_block_start := iterated_fold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (destIdx := midIdx)
    (h_destIdx := h_midIdx) (h_destIdx_le := by omega)
    (f := f_block_start) (r_challenges := r_challenges)

  if h_is_close : (fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ)
      h_destIdx h_destIdx_le (f := f_block_start)) then
    let f_bar_block_start := UDRCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      block_start_idx (f := f_block_start)
      (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β
        block_start_idx ϑ h_destIdx h_destIdx_le
        f_block_start h_is_close)

    let folded_f_bar_block_start := iterated_fold 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := k)
      (h_destIdx := h_midIdx) (h_destIdx_le := by omega)
      (f := f_bar_block_start) (r_challenges := r_challenges)

    ¬ (fiberwiseDisagreementSet 𝔽q β
          block_start_idx ϑ h_destIdx h_destIdx_le
          f_block_start f_bar_block_start
        ⊆
        fiberwiseDisagreementSet 𝔽q β
          midIdx (ϑ - k) h_midIdx_to_block h_destIdx_le
          folded_f_block_start folded_f_bar_block_start)
  else
    fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := ϑ - k)
      (h_destIdx := h_midIdx_to_block)
      (h_destIdx_le := h_destIdx_le)
      (f := folded_f_block_start)

omit [CharP L 2] in
/-- When all folding steps have been applied (`k = ϑ`), the incremental bad event
coincides with the full `foldingBadEvent`. -/
@[simp]
lemma incrementalFoldingBadEvent_of_k_eq_0_is_false
    (block_start_idx : Fin r) (k : ℕ) (h_k : k = 0) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = block_start_idx.val) (h_destIdx : destIdx = block_start_idx + ϑ)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_challenges : Fin k → L) :
    ¬(incrementalFoldingBadEvent 𝔽q β (block_start_idx := block_start_idx) (ϑ := ϑ)
      (k := k) (h_k_le := by omega) (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by omega) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      f_block_start r_challenges) := by
  subst h_k
  unfold incrementalFoldingBadEvent
  simp only [tsub_zero]
  by_cases h_close : fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ)
      h_destIdx h_destIdx_le (f := f_block_start)
  · simp only [h_close, ↓reduceDIte]
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega)]
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega)]
    rw [fiberwiseDisagreementSet_congr_sourceDomain_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (sourceIdx₁ := block_start_idx)
      (sourceIdx₂ := midIdx) (h_sourceIdx_eq := by omega)]
    simp only [subset_refl, not_true_eq_false, not_false_eq_true]
  · simp only [h_close, ↓reduceDIte]
    rw [fiberwiseClose_congr_sourceDomain_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (sourceIdx₁ := block_start_idx) (sourceIdx₂ := midIdx) (h_sourceIdx_eq := by omega)]
      at h_close
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f_block_start)
      (r_challenges := r_challenges)]
    exact h_close

omit [CharP L 2] in
/-- When all folding steps have been applied (`k = ϑ`), the incremental bad event
coincides with the full `foldingBadEvent`. -/
lemma incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
    (block_start_idx : Fin r) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = destIdx.val) (h_destIdx : destIdx = block_start_idx + ϑ)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_challenges : Fin ϑ → L) :
    incrementalFoldingBadEvent 𝔽q β block_start_idx ϑ (h_k_le := le_refl ϑ)
      (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by omega) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        f_block_start r_challenges ↔
    foldingBadEvent 𝔽q β block_start_idx ϑ h_destIdx h_destIdx_le
      f_block_start r_challenges := by
  unfold incrementalFoldingBadEvent foldingBadEvent
  simp only [show ϑ ≠ 0 from NeZero.ne ϑ, ↓reduceDIte, Nat.sub_self]
  have h_midIdx_eq_destIdx : midIdx = destIdx := by omega
  subst h_midIdx_eq_destIdx
  by_cases h_close : fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ)
      h_destIdx h_destIdx_le (f := f_block_start)
  · simp only [h_close, ↓reduceDIte]
    rw [fiberwiseDisagreementSet_steps_zero_eq_disagreementSet]
  · simp only [h_close, ↓reduceDIte]
    rw [fiberwiseClose_steps_zero_iff_UDRClose]

end SoundnessTools
end Binius.BinaryBasefold
