/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module


public import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Binary Basefold compliance and folding bad events

## Main definitions

* `IsCompliant`: the compliance of an oracle with the next one ([DP24] Definition 4.18).
* `FoldingBadEvent`: the folding bad event ([DP24] Definition 4.20), and
  `IncrementalFoldingBadEvent`, its refinement to the first `k` challenges of a block, which is
  `False` at `k = 0` and equals `FoldingBadEvent` at `k = ϑ`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
-/

@[expose] public section




namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Code ReedSolomon BerlekampWelch ProbabilityTheory

noncomputable section SoundnessTools

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
local instance instFactPrimeRingCharCompliance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/--
Compliance: for an index `i` that is a multiple of `steps`,
the oracle `f_i` is compliant if it's close to the code fiber-wise, the next oracle
`f_i_plus_steps` is close to its code, and their unique closest codewords are consistent
with folding.
-/
def IsCompliant (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (challenges : Fin steps → L) : Prop :=
  ∃ (h_fw_dist_lt : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (f := f_i))
    (h_dist_next_lt : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx)  (f := f_i_plus_steps)),
    let h_dist_curr_lt := uniqueDecodingClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_destIdx h_destIdx_le f_i
      (h_fw_dist_lt := h_fw_dist_lt)
    let f_bar_i := uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := by omega) (f := f_i) (h_within_radius := h_dist_curr_lt)
    let f_bar_i_plus_steps := uniqueDecodingCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := by omega)
      f_i_plus_steps h_dist_next_lt
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
      h_destIdx h_destIdx_le
      f_bar_i challenges = f_bar_i_plus_steps

open Classical in
/-- The folding bad event. It captures two scenarios where the
random folding challenges undermine the protocol's soundness checks.
For `i ∈ {0, ..., ℓ - steps}`,
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ₊steps / 2` (fiberwise close):
  `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾)` is not contained in the disagreement set of the two folded oracles,
  i.e. fiberwiseDisagreementSet ⊄ foldedDisagreementSet
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ dᵢ₊steps / 2`  (fiberwise far):
  `d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`, i.e. foldedUDRClose
-/
def FoldingBadEvent (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) : Prop :=
  let folded_f_i := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
    (r_challenges := r_challenges)
  if h_is_close : (FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_destIdx h_destIdx_le (f := f_i)) then
    let f_bar_i := uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i (h_i := by omega) (f := f_i)
      (h_within_radius := uniqueDecodingClose_of_fiberwiseClose 𝔽q β i steps h_destIdx
        h_destIdx_le f_i h_is_close)
    let folded_f_bar_i := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_bar_i) (r_challenges := r_challenges)
    ¬ (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le (f := f_i) (g := f_bar_i) ⊆
       disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
         (f := folded_f_i) (g := folded_f_bar_i))
  else
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
       (f := folded_f_i)

open Classical in
/-- The incremental folding bad event, the partial-block refinement of `FoldingBadEvent`.
For block start index `block_start_idx`, block size `ϑ`, and **partial step count**
`k ≤ ϑ`, with `destIdx = block_start_idx + ϑ` (the block destination),
`E(block_start_idx, k)` is defined as follows:

At `k = 0`, this event is impossible (`not_incrementalFoldingBadEvent_zero`).
- Case 1 (fiberwise close at block level):
  `Δ⁽ⁱ⁾(f, f̄) ⊄ Δ⁽ⁱ⁺ᵏ⁾(fold_k(f), fold_k(f̄))`
  where both sides are projected to `S^{i+ϑ}` (the block destination).
- Case 2 (fiberwise far at block level):
  `d⁽ⁱ⁺ᵏ⁾(fold_k(f), C⁽ⁱ⁺ᵏ⁾) < d_{i+ϑ}/2`
  where `d⁽ⁱ⁺ᵏ⁾` is the fiberwise distance projected to `S^{i+ϑ}`.

When `k = ϑ`, this coincides with `FoldingBadEvent`. -/
def IncrementalFoldingBadEvent
    (block_start_idx : Fin r) {midIdx destIdx : Fin r} (k : ℕ)
    (h_k_le : k ≤ ϑ) (h_midIdx : midIdx = block_start_idx + k)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_challenges : Fin k → L) : Prop :=
  have h_ik_le : block_start_idx.val + k ≤ ℓ := by omega
  have h_midIdx_to_block : destIdx = midIdx + (ϑ - k) := by omega
  let folded_f_block_start := iteratedFold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (destIdx := midIdx)
    (h_destIdx := h_midIdx) (h_destIdx_le := by omega)
    (f := f_block_start) (r_challenges := r_challenges)
  if h_is_close : (FiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ)
      h_destIdx h_destIdx_le (f := f_block_start)) then
    let f_bar_block_start := uniqueDecodingCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      block_start_idx (h_i := by omega) (f := f_block_start)
      (h_within_radius := uniqueDecodingClose_of_fiberwiseClose 𝔽q β
        block_start_idx ϑ h_destIdx h_destIdx_le
        f_block_start h_is_close)
    let folded_f_bar_block_start := iteratedFold 𝔽q β
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
    FiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := ϑ - k)
      (h_destIdx := h_midIdx_to_block)
      (h_destIdx_le := h_destIdx_le)
      (f := folded_f_block_start)

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Before any folding steps (`k = 0`), the incremental bad event is false. -/
@[simp]
lemma not_incrementalFoldingBadEvent_zero
    (block_start_idx : Fin r) (k : ℕ) (h_k : k = 0) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = block_start_idx.val) (h_destIdx : destIdx = block_start_idx + ϑ)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_challenges : Fin k → L) :
    ¬(IncrementalFoldingBadEvent 𝔽q β (block_start_idx := block_start_idx) (ϑ := ϑ)
      (k := k) (h_k_le := by omega) (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by omega) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      f_block_start r_challenges) := by
  subst h_k
  unfold IncrementalFoldingBadEvent
  simp only [tsub_zero]
  by_cases h_close : FiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ)
      h_destIdx h_destIdx_le (f := f_block_start)
  · simp only [h_close, ↓reduceDIte]
    rw [iteratedFold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega)]
    rw [iteratedFold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega)]
    rw [fiberwiseDisagreementSet_congr_sourceDomain_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (sourceIdx₁ := block_start_idx)
      (sourceIdx₂ := midIdx) (h_sourceIdx_eq := by omega)]
    simp only [subset_refl, not_true_eq_false, not_false_eq_true]
  · simp only [h_close, ↓reduceDIte]
    rw [fiberwiseClose_congr_sourceDomain_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (sourceIdx₁ := block_start_idx) (sourceIdx₂ := midIdx) (h_sourceIdx_eq := by omega)]
      at h_close
    rw [iteratedFold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f_block_start)
      (r_challenges := r_challenges)]
    exact h_close

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- When all folding steps have been applied (`k = ϑ`), the incremental bad event
coincides with the full `FoldingBadEvent`. -/
lemma incrementalFoldingBadEvent_full_iff
    (block_start_idx : Fin r) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = destIdx.val) (h_destIdx : destIdx = block_start_idx + ϑ)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_challenges : Fin ϑ → L) :
    IncrementalFoldingBadEvent 𝔽q β block_start_idx ϑ (h_k_le := le_refl ϑ)
      (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by omega) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        f_block_start r_challenges ↔
    FoldingBadEvent 𝔽q β block_start_idx ϑ h_destIdx h_destIdx_le
      f_block_start r_challenges := by
  unfold IncrementalFoldingBadEvent FoldingBadEvent
  simp only [Nat.sub_self]
  have h_midIdx_eq_destIdx : midIdx = destIdx := by omega
  subst h_midIdx_eq_destIdx
  by_cases h_close : FiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ)
      h_destIdx h_destIdx_le (f := f_block_start)
  · simp only [h_close, ↓reduceDIte]
    rw [fiberwiseDisagreementSet_steps_zero_eq_disagreementSet]
  · simp only [h_close, ↓reduceDIte]
    rw [fiberwiseClose_steps_zero_iff_uniqueDecodingClose]

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Transport an incremental folding event along equal step counts, indices and challenges. -/
lemma incrementalFoldingBadEvent_congr
    (block_start_idx : Fin r) {midIdx midIdx' destIdx : Fin r} {k k' : ℕ}
    (hmid : midIdx = midIdx') (hk : k = k')
    (h_k_le : k ≤ ϑ) (h_k_le' : k' ≤ ϑ)
    (h_midIdx : midIdx = block_start_idx + k)
    (h_midIdx' : midIdx' = block_start_idx + k')
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (rs : Fin k → L) (rs' : Fin k' → L) (hrs : HEq rs rs') :
    IncrementalFoldingBadEvent 𝔽q β block_start_idx k h_k_le h_midIdx h_destIdx h_destIdx_le
      f rs ↔
    IncrementalFoldingBadEvent 𝔽q β block_start_idx k' h_k_le' h_midIdx' h_destIdx h_destIdx_le
      f rs' := by
  cases hmid
  cases hk
  cases hrs
  rfl

end SoundnessTools
end Binius.BinaryBasefold
