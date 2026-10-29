/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.DG25.ReedSolomon
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
# Binary Basefold: the per-challenge bound on the incremental folding bad event

`IncrementalFoldingBadEvent` (`Compliance`) is the folding bad event of a block of `ϑ` folds,
restricted to the first `k` challenges of the block. The main statement,
`prob_incrementalFoldingBadEvent_fresh_le`, bounds, for a fixed block start, a fixed oracle and a
fixed prefix of `k < ϑ` challenges, the probability over one fresh uniform challenge that the
event holds at `k + 1` but not at `k`, by `|S⁽ⁱ⁺ᶿ⁾| / |L|`. The fold step's round-by-round
knowledge soundness consumes it one challenge at a time.

## Main statements

* `prob_incrementalFoldingBadEvent_fresh_le_of_fiberwiseClose`: the case where the block's oracle
  is fiberwise close. A fold step can drop a point of the fiberwise disagreement set only at a
  root of a nonzero polynomial of degree at most one in the fresh challenge; a union bound over
  the destination domain finishes.
* `prob_incrementalFoldingBadEvent_fresh_le_of_not_fiberwiseClose`: the far case. The
  tensor-combine stack of the current fold is far from the interleaved code
  (`preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose`), hence so is the pair of its
  even and odd rows (`jointProximityNat_of_jointProximityNat₂_splitEvenOdd`); one fold step is
  the affine line through that pair
  (`preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd`), and the affine-line
  proximity gap of Reed–Solomon codes, lifted to interleaved codes, bounds the probability
  (`prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂`).
* `prob_incrementalFoldingBadEvent_fresh_le`: the two cases together.

## Relation to [DP24]

[DP24] Proposition 4.21 bounds the probability mass of the whole bad set `Eᵢ ⊂ Lᶿ`
(Definition 4.20) by `ϑ · |S⁽ⁱ⁺ᶿ⁾| / |L|`. The incremental event is `False` at `k = 0` and is the
folding bad event at `k = ϑ` (`Compliance`), so summing the per-challenge bound over the `ϑ`
challenges of a block recovers that bound, for `ℓ + 𝓡 < r` as everywhere in Binius ([DP24] §4.1
also allows `ℓ + R = r`; the strict bound comes from CompPoly's `Fin r`-indexed subspaces `U`
behind `sDomain`). The per-challenge statement itself is not in [DP24]; it is specific to this
development. Its two cases follow the
two cases of the paper's proof, one challenge at a time: the paper applies the Schwartz–Zippel
lemma to all `ϑ` challenges in the close case, and the tensor proximity gap ([DP24] Theorem 2.4)
after Lemma 4.22 in the far case; here the far case uses the affine-line gap ([DP24] Theorem 2.3)
lifted to interleaved codes ([DG25], `affine_gaps_lifted_to_interleaved_codes`).

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
* [Diamond, B.E. and Gruen, A., *Proximity Gaps in Interleaved Codes*][DG25]
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory
open Probability

/-- A nonzero difference on two distinct fiber points vanishes after folding for at most one
challenge. -/
private lemma fold_affine_eq_zero_unique {F : Type} [CommRing F] [NoZeroDivisors F]
    (x₀ x₁ Δ₀ Δ₁ a b : F) (hx : x₀ ≠ x₁) (hΔ : Δ₀ ≠ 0 ∨ Δ₁ ≠ 0)
    (ha : Δ₀ * ((1 - a) * x₁ - a) + Δ₁ * (a - (1 - a) * x₀) = 0)
    (hb : Δ₀ * ((1 - b) * x₁ - b) + Δ₁ * (b - (1 - b) * x₀) = 0) : a = b := by
  let A := Δ₀ * x₁ - Δ₁ * x₀
  let C := Δ₁ * (1 + x₀) - Δ₀ * (1 + x₁)
  have ha' : A + a * C = 0 := by dsimp [A, C]; linear_combination ha
  have hb' : A + b * C = 0 := by dsimp [A, C]; linear_combination hb
  have hprod : (a - b) * C = 0 := by linear_combination ha' - hb'
  rcases mul_eq_zero.mp hprod with hab | hC
  · exact sub_eq_zero.mp hab
  · have hA : A = 0 := by simpa only [hC, mul_zero, add_zero] using ha'
    have hΔeq : Δ₀ = Δ₁ := by dsimp [A] at hA; dsimp [C] at hC; linear_combination -hA - hC
    have hmul : Δ₀ * (x₁ - x₀) = 0 := by
      dsimp [A] at hA
      rw [← hΔeq] at hA
      simpa only [mul_sub] using hA
    have hzero := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hx.symm)
    exact (hΔ.elim (fun h => h hzero) (fun h => h (hΔeq ▸ hzero))).elim

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

section Prelims

open Classical in
omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- If the pair `(u₀, u₁)` is not `e`-close to the interleaved destination code, with `e` within
the unique-decoding radius, then the affine line `(1 - r) • u₀ + r • u₁` is `e`-close to that
code with probability at most `|S| / |L|` over a uniform `r`. This is the contrapositive of the
affine-line proximity gap of Reed–Solomon codes
(`ReedSolomon_ProximityGapAffineLines_UniqueDecoding`, with false-witness bound `|S|`) lifted
to interleaved codes
(`affine_gaps_lifted_to_interleaved_codes`). -/
lemma prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂
    {m : ℕ} {destIdx : Fin r} (h_destIdx_le : destIdx ≤ ℓ)
    (u₀ u₁ : Word (InterleavedSymbol L (Fin m))
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx))
    (e : ℕ) (he : e ≤ Code.uniqueDecodingRadius
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (F := L)
      (C := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))
    (h_far : ¬ jointProximityNat₂ (A := InterleavedSymbol L (Fin m))
      (C := ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m)))
      (u₀ := u₀) (u₁ := u₁) (e := e)) :
    Pr{let r ← $ᵗ L}[
      Δ₀(affineLineEvaluation (F := L) u₀ u₁ r,
        ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m))) ≤ e]
    ≤ (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ℝ≥0) / (Fintype.card L) := by
  by_contra h_prob_gt_bound
  apply h_far
  let S_dest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let α := Embedding.subtype fun (x : L) ↦ x ∈ S_dest
  let C_dest := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let RS_dest := ReedSolomon.code α (2^(ℓ - destIdx.val))
  have h_RS_affine := ReedSolomon_ProximityGapAffineLines_UniqueDecoding
    (A := L) (ι := S_dest) (α := α) (k := 2^(ℓ - destIdx.val))
    (hk := by
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx)
        (h_i := lt_rounds_add_rate_of_le_rounds (by exact h_destIdx_le))]
      calc 2 ^ (ℓ - destIdx.val) ≤ 2 ^ (ℓ + 𝓡 - destIdx.val) :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ = Fintype.card 𝔽q ^ (ℓ + 𝓡 - destIdx.val) := by rw [hF₂.out])
    e (by exact he)
  have h_lifted := affine_gaps_lifted_to_interleaved_codes (A := L)
    (F := L) (ι := S_dest) (MC := RS_dest) (m := m)
    (e := e) (he := he) (ε := Fintype.card S_dest)
    (hε := by
      have h_dist_pos : 0 < ‖(C_dest : Set (S_dest → L))‖₀ := by
        simpa only [C_dest, codeDistance] using codeDistance_pos 𝔽q β destIdx
      have : NeZero ‖(C_dest : Set (S_dest → L))‖₀ := NeZero.of_pos h_dist_pos
      have h_2e_lt_d : 2 * e < ‖(C_dest : Set (S_dest → L))‖₀ := by
        exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
          (C := (C_dest : Set (S_dest → L))) (e := e)).1 (by
            exact he)
      have h_e_add_one_le_d : e + 1 ≤ ‖(C_dest : Set (S_dest → L))‖₀ := by
        omega
      have h_d_le_card : ‖(C_dest : Set (S_dest → L))‖₀ ≤ Fintype.card S_dest := by
        exact Code.dist_le_card (C := (C_dest : Set (S_dest → L)))
      exact le_trans h_e_add_one_le_d h_d_le_card)
    h_RS_affine
  exact h_lifted u₀ u₁ (by
    rw [ENNReal.coe_natCast]
    rw [not_le] at h_prob_gt_bound
    exact h_prob_gt_bound)

end Prelims

omit [SampleableType L] [DecidableEq 𝔽q] [NeZero ℓ] [NeZero ϑ] hdiv in
/-- A fiber that still contains a disagreement after the fixed prefix disappears for at most
one value of the next challenge. -/
private lemma card_disappearing_fiber_le_one
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r}
    (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i f_bar_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    (h_y : y ∈ fiberwiseDisagreementSet 𝔽q β midIdx_i (ϑ - k) (by omega) h_destIdx_le
      (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := block_start_idx) (steps := k) h_midIdx_i (by omega) f_i r_prefix)
      (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := block_start_idx) (steps := k) h_midIdx_i (by omega) f_bar_i r_prefix)) :
    (Finset.filter (fun r_new =>
        y ∉ fiberwiseDisagreementSet 𝔽q β
            midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
            (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_i) (r_challenges := Fin.snoc r_prefix r_new))
            (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_new)))
        Finset.univ).card ≤ 1 := by
  classical
  let fold_k_f := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) h_midIdx_i (by omega) f_i r_prefix
  let fold_k_f_bar := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) h_midIdx_i (by omega) f_bar_i r_prefix
  have h_decomp (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      block_start_idx) (r_new : L) :=
    iteratedFold_snoc 𝔽q β block_start_idx k h_midIdx_i h_midIdx_i_succ
      (by omega : midIdx_i_succ.val ≤ ℓ) f r_prefix r_new
  have h_exists_disagreeing_w :
      ∃ w : sDomain 𝔽q β h_ℓ_add_R_rate midIdx_i_succ,
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
          (i := midIdx_i_succ) (k := ϑ - (k + 1))
          (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) w = y) ∧
        (let fiberMap := quotientFiber 𝔽q β (i := midIdx_i) (steps := 1)
          (h_destIdx := by omega) (h_destIdx_le := by omega) (y := w)
        let x₀ := fiberMap 0
        let x₁ := fiberMap 1
        (fold_k_f x₀ ≠ fold_k_f_bar x₀ ∨ fold_k_f x₁ ≠ fold_k_f_bar x₁)) := by
    have hy_in_disagr := h_y
    simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy_in_disagr
    obtain ⟨z, hz_quotient, hz_ne⟩ := hy_in_disagr
    let w : sDomain 𝔽q β h_ℓ_add_R_rate midIdx_i_succ :=
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := midIdx_i) (k := 1) (h_destIdx := by omega)
        (h_destIdx_le := by omega) z
    refine ⟨w, ?_, ?_⟩
    · -- iteratedQuotientMap(w, midIdx_i_succ → destIdx) = y
      have h_factor := iteratedQuotientMap_succ_comp 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx_i) (midIdx := midIdx_i_succ) (destIdx := destIdx)
        (steps := ϑ - k - 1) (h_midIdx := by omega)
        (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) z
      rw [←hz_quotient]
      have h_factor_congr := iteratedQuotientMap_congr_k 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx_i) (k₁ := (ϑ - k - 1) + 1) (k₂ := ϑ - k)
        (hk := by omega) (h_destIdx₁ := by omega) (h_destIdx₂ := by omega)
        (h_destIdx_le := h_destIdx_le) z
      rw [← h_factor_congr, h_factor]
    · -- z is one of x₀ or x₁ in the fiber of w, hence fold_k disagreement
      intro fiberMap x₀ x₁
      have h_midIdx_i_succ_le : midIdx_i_succ.val ≤ ℓ := by omega
      have hw_eq : w = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
          (i := midIdx_i) (k := 1) (h_destIdx := by omega)
          (h_destIdx_le := h_midIdx_i_succ_le) z := rfl
      have hz_fiber := (eq_iteratedQuotientMap_iff_quotientFiber_apply_eq 𝔽q β
        (i := midIdx_i) (steps := 1) (h_destIdx := by omega)
        (h_destIdx_le := h_midIdx_i_succ_le)
        z w).mp hw_eq
      set idx := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx_i) (steps := 1) (h_destIdx := by omega)
        (h_destIdx_le := h_midIdx_i_succ_le) z with h_idx_def
      have hz_eq : fiberMap idx = z := hz_fiber
      by_cases h0 : idx = 0
      · left; rw [h0] at hz_eq
        change fold_k_f (fiberMap 0) ≠ fold_k_f_bar (fiberMap 0)
        rw [hz_eq]; exact hz_ne
      · right; have h1 : idx = 1 := Fin.eq_one_of_ne_zero idx h0
        rw [h1] at hz_eq
        change fold_k_f (fiberMap 1) ≠ fold_k_f_bar (fiberMap 1)
        rw [hz_eq]; exact hz_ne
  obtain ⟨w, hw_in_fiber, hw_disagree⟩ := h_exists_disagreeing_w
  let fiberMap_w := quotientFiber 𝔽q β (i := midIdx_i) (steps := 1)
    (h_destIdx := by omega) (h_destIdx_le := by omega) (y := w)
  let x₀ := fiberMap_w 0
  let x₁ := fiberMap_w 1
  let Δ₀ := fold_k_f x₀ - fold_k_f_bar x₀
  let Δ₁ := fold_k_f x₁ - fold_k_f_bar x₁
  have h_fold_diff : ∀ r_new : L,
      fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
        (f := fold_k_f) (r_chal := r_new) w
      - fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
        (f := fold_k_f_bar) (r_chal := r_new) w
      = Δ₀ * ((1 - r_new) * x₁.val - r_new)
      + Δ₁ * (r_new - (1 - r_new) * x₀.val) := by
    intro r_new
    simp only [fold, Δ₀, Δ₁, x₀, x₁, fiberMap_w]
    ring
  have h_Δ_ne_zero : Δ₀ ≠ 0 ∨ Δ₁ ≠ 0 := by
    rcases hw_disagree with h0 | h1
    · left; exact sub_ne_zero.mpr h0
    · right; exact sub_ne_zero.mpr h1
  have h_x₀_ne_x₁ : (x₀ : L) ≠ (x₁ : L) := by
    have h_inj := quotientFiber_injective 𝔽q β midIdx_i 1
      (by omega) (by omega : midIdx_i_succ.val ≤ ℓ) w
    have h_ne : (0 : Fin (2 ^ 1)) ≠ 1 := by decide
    exact Subtype.val_injective.ne (h_inj.ne h_ne)
  have h_at_most_one_root :=
    fun a b => fold_affine_eq_zero_unique x₀.val x₁.val Δ₀ Δ₁ a b h_x₀_ne_x₁ h_Δ_ne_zero
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h_agree_at_w : ∀ (r_val : L),
      y ∉ fiberwiseDisagreementSet 𝔽q β
        midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
        (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k + 1)
          (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
          (f := f_i) (r_challenges := Fin.snoc r_prefix r_val))
        (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k + 1)
          (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
          (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_val)) →
      fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
        (f := fold_k_f) (r_chal := r_val) w
      = fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
        (f := fold_k_f_bar) (r_chal := r_val) w := by
    intro r_val h_not_in
    rw [h_decomp f_i r_val, h_decomp f_bar_i r_val] at h_not_in
    simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and, not_exists, not_and] at h_not_in
    exact not_not.mp (h_not_in w hw_in_fiber)
  have h_agree_a := h_agree_at_w a ha
  have h_agree_b := h_agree_at_w b hb
  have h_poly_zero_a : Δ₀ * ((1 - a) * x₁.val - a) + Δ₁ * (a - (1 - a) * x₀.val) = 0 := by
    rw [← h_fold_diff a, sub_eq_zero]; exact h_agree_a
  have h_poly_zero_b : Δ₀ * ((1 - b) * x₁.val - b) + Δ₁ * (b - (1 - b) * x₀.val) = 0 := by
    rw [← h_fold_diff b, sub_eq_zero]; exact h_agree_b
  exact h_at_most_one_root a b h_poly_zero_a h_poly_zero_b

open Classical in
omit [NeZero ℓ] hdiv in
omit [DecidableEq 𝔽q] in
omit [NeZero ϑ] in
/-- The per-challenge bound on the incremental folding bad event when the block's oracle
`f⁽ⁱ⁾` is fiberwise close, with decoded codeword `f̄⁽ⁱ⁾`. Write `fₖ`, `f̄ₖ` for their folds at
the fixed prefix of `k` challenges.

The event at `k` fails when the fiberwise disagreement set `Δ` of `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` is contained
in that of `fₖ` and `f̄ₖ`; it holds at `k + 1` when some `y ∈ Δ` leaves the disagreement set after
one more fold with the fresh challenge `r`. For such `y`, the difference `fₖ - f̄ₖ` is nonzero
somewhere on the fiber of `y`, and on each pair of points of the next fiber the difference of
the folds is `a + (b - a) · r`, where `(a, b)` is the image of the nonzero difference vector under
the invertible fold matrix. This vanishes for at most one `r`, so `y` drops out with probability
at most `1 / |L|`, and a union bound over `Δ ⊆ S⁽ⁱ⁺ᶿ⁾` gives `|S⁽ⁱ⁺ᶿ⁾| / |L|`. -/
lemma prob_incrementalFoldingBadEvent_fresh_le_of_fiberwiseClose
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_close : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr{ let r_new ← $ᵗ L }[
      ¬ IncrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      IncrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ)
        (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  classical
  dsimp only [IncrementalFoldingBadEvent]
  have h_k_succ_ne_0 : ¬(k + 1 = 0) := by omega
  simp only [h_block_close, ↓reduceDIte]
  let f_i := f_block_start
  let f_bar_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx :=
    uniqueDecodingCodeword 𝔽q β (i := block_start_idx) (h_i := by omega)
      (f := f_i) (h_within_radius := uniqueDecodingClose_of_fiberwiseClose 𝔽q β
        block_start_idx ϑ h_destIdx h_destIdx_le f_i h_block_close)
  let Δ_fiber : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
    fiberwiseDisagreementSet 𝔽q β (i := block_start_idx) ϑ h_destIdx h_destIdx_le f_i f_bar_i
  let fold_k_f := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_i) (r_challenges := r_prefix)
  let fold_k_f_bar := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_bar_i) (r_challenges := r_prefix)
  let not_Ek := Δ_fiber ⊆ fiberwiseDisagreementSet 𝔽q β
    midIdx_i (ϑ - k) (by omega) h_destIdx_le fold_k_f fold_k_f_bar
  let afterDisagreement (r_new : L) :=
    fiberwiseDisagreementSet 𝔽q β midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
      (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := block_start_idx) (steps := k + 1) h_midIdx_i_succ (by omega) f_i
        (Fin.snoc r_prefix r_new))
      (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := block_start_idx) (steps := k + 1) h_midIdx_i_succ (by omega) f_bar_i
        (Fin.snoc r_prefix r_new))
  by_cases h_not_Ek : not_Ek
  swap
  · apply le_trans (prEvent_mono ($ᵗ L) _ (fun _ => False)
      (fun r_new h => absurd (not_not.mp h.1) h_not_Ek))
    simp
  · apply le_trans (prEvent_mono ($ᵗ L) _ _ (fun r_new h => h.2))
    let L_card := Fintype.card L
    rw [SampleableType.prEvent_uniformSample]
    have h_per_point_card : ∀ y ∈ Δ_fiber,
      (Finset.filter (fun r_new =>
        y ∉ afterDisagreement r_new)
        Finset.univ).card ≤ 1 := by
      intro y hy
      exact card_disappearing_fiber_le_one 𝔽q β block_start_idx k h_k_lt
        h_midIdx_i h_midIdx_i_succ h_destIdx h_destIdx_le f_i f_bar_i r_prefix y (h_not_Ek hy)
    have h_bad_subset : (Finset.filter (fun r_new =>
        ¬(↑Δ_fiber ⊆ ↑(afterDisagreement r_new)))
        Finset.univ) ⊆
      Δ_fiber.biUnion (fun y =>
        Finset.filter (fun r_new =>
          y ∉ afterDisagreement r_new)
        Finset.univ) := by
      intro r_new hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.not_subset] at hr
      rcases hr with ⟨y, hy_mem, hy_not_in⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨y, hy_mem, hy_not_in⟩
    calc ((Finset.filter _ Finset.univ).card : ENNReal) / (L_card : ENNReal)
        _ ≤ (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ENNReal) / L_card := by
          gcongr
          calc (Finset.filter _ Finset.univ).card
              _ ≤ (Δ_fiber.biUnion _).card := Finset.card_le_card h_bad_subset
              _ ≤ ∑ y ∈ Δ_fiber, (Finset.filter _ Finset.univ).card := Finset.card_biUnion_le
              _ ≤ ∑ _ ∈ Δ_fiber, 1 := Finset.sum_le_sum (fun y hy => h_per_point_card y hy)
              _ = Δ_fiber.card := by simp
              _ ≤ Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := Finset.card_le_univ _

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
omit [SampleableType L] in
/-- One fold step on a tensor-combine stack is the affine line through its even and odd rows.
If `U` is the stack of `f_i` over `steps + 1` folds, with even rows `U_even` and odd rows
`U_odd` (`splitEvenOddRowWiseInterleavedWords`), then the stack over the remaining `steps` folds
of `fold f_i r_new` is `affineLineEvaluation (⋈|U_even) (⋈|U_odd) r_new`: folding
consumes the first challenge, which pairs rows `2j` and `2j + 1`. -/
lemma preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩)
    (r_new : L) :
    have h_midIdx_lt_ℓ : midIdx.val < ℓ := by
      have := NeZero.pos steps; omega
    let U := preTensorCombine 𝔽q β i (steps + 1)
      (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := steps) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := steps) U).2
    let fold_1_f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ (destIdx := midIdx) (h_destIdx := h_midIdx)
      (h_destIdx_le := by omega) f_i r_new
    let midIdx_fin_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    let V := preTensorCombine 𝔽q β midIdx_fin_ℓ steps
      (destIdx := destIdx)
      (h_destIdx := by simp [midIdx_fin_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le) (by exact fold_1_f)
    interleaveWordStack V =
      affineLineEvaluation (F := L)
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new := by
  intro h_midIdx_lt_ℓ U U_even U_odd fold_1_f midIdx_fin_ℓ V
  have h_fold_eq_U (r_chal : Fin (steps + 1) → L) :=
    iteratedFold_eq_multilinearCombine_preTensorCombine 𝔽q β i (steps + 1)
      h_destIdx h_destIdx_le f_i r_chal
  have h_fold_eq_V (r_chal : Fin steps → L) :=
    iteratedFold_eq_multilinearCombine_preTensorCombine 𝔽q β midIdx_fin_ℓ steps
      (by dsimp [midIdx_fin_ℓ]; omega) h_destIdx_le fold_1_f r_chal
  have h_indicator : ∀ (W : WordStack L (Fin (2 ^ steps))
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) (j' : Fin (2 ^ steps))
      (y' : sDomain 𝔽q β h_ℓ_add_R_rate destIdx),
      multilinearCombine (F := L) W (bitsOfIndex j') y' = W j' y' := by
    intro W' j' y'
    simp [multilinearCombine, multilinearWeight_bitsOfIndex_fun]
  have h_recursive : ∀ r_chal : Fin (steps + 1) → L,
      multilinearCombine U r_chal =
      multilinearCombine (affineLineEvaluation (F := L) U_even U_odd (r_chal 0))
        (fun k => r_chal (Fin.succ k)) := by
    intro r_chal
    dsimp [U_even, U_odd]
    exact multilinearCombine_recursive_form_first (u := U) (r_challenges := r_chal)
  ext y j
  change V j y = affineLineEvaluation U_even U_odd r_new j y
  rw [←h_indicator V j y]
  conv_lhs => rw [←h_fold_eq_V (bitsOfIndex j)]
  have h_first :
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps + 1) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := f_i)
        (r_challenges := Fin.cons r_new (bitsOfIndex j)) =
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx) (steps := steps) (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le) (f := fold_1_f)
        (r_challenges := bitsOfIndex j) := by
    change
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps + 1) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := f_i)
        (r_challenges := Fin.cons r_new (bitsOfIndex j)) =
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx) (steps := steps) (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le)
        (f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := midIdx) (h_destIdx := h_midIdx)
          (h_destIdx_le := by omega) f_i r_new)
        (r_challenges := bitsOfIndex j)
    have h_first_raw :=
      iteratedFold_first 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i, by omega⟩ (steps := steps) h_midIdx h_destIdx h_destIdx_le f_i
        (Fin.cons r_new (bitsOfIndex j))
    exact h_first_raw
  rw [←h_first]
  rw [h_fold_eq_U (Fin.cons r_new (bitsOfIndex j))]
  rw [h_recursive (Fin.cons r_new (bitsOfIndex j))]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [h_indicator (affineLineEvaluation (F := L) U_even U_odd r_new) j y]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- A single fold of `f_i` is the multilinear combination, at the fold challenge, of the
two-row tensor-combine stack of `f_i`. -/
lemma fold_eq_multilinearCombine_preTensorCombine
    (i : Fin ℓ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_new : L) :
    let U := preTensorCombine 𝔽q β i 1
      (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) f_i
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) f_i r_new
    = multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
  intro U
  ext y
  rw [fold_eq_foldMatrixForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (destIdx := destIdx) (h_destIdx := by omega)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (r_challenge := r_new)]
  unfold foldMatrixForm multilinearCombine
  dsimp [U]
  have h_blk :
      blockDiagMatrix (L := L) (n := 0)
        (Mz₀ := (1 : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) L))
        (Mz₁ := (1 : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) L))
      = (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) L) := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [blockDiagMatrix, reindexSquareMatrix, from4Blocks]
  simp only [Fin.isValue, butterflyMatrix_zero_apply, cons_mulVec,
    cons_dotProduct, neg_mul, dotProduct_of_isEmpty, add_zero, one_mul, empty_mulVec,
    Matrix.dotProduct_cons, preTensorCombine, reducePow, foldMatrix, reduceAdd,
    Nat.add_zero, h_blk, mul_one, Fin.sum_univ_two, cons_val_zero, cons_val_one, cons_val_fin_one]
  have h_w0 :
      vecHead (multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new)) =
        multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new) 0 := by
    rfl
  have h_w1 :
      vecHead (vecTail (multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new))) =
        multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new) 1 := by
    rfl
  rw [h_w0, h_w1]

omit [DecidableEq 𝔽q] in
omit [NeZero ℓ] in
omit [SampleableType L] in
/-- If the single fold `fold f_i r_new` is fiberwise close over the remaining `s` folds, then the
affine line at `r_new` through the even and odd rows of the stack of `f_i` over `s + 1` folds is
within the unique-decoding radius of the interleaved destination code. -/
lemma distFromCode_affineLineEvaluation_le_of_fiberwiseClose_fold
    (i : Fin r) (h_i_lt_ℓ : i.val < ℓ) (s : ℕ)
    {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (s + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_new : L)
    (h_fw_close : FiberwiseClose 𝔽q β midIdx s
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i (destIdx := midIdx) (h_destIdx := h_midIdx)
        (h_destIdx_le := by omega) f_i r_new)) :
    let i_ℓ : Fin ℓ := ⟨i.val, h_i_lt_ℓ⟩
    let U := preTensorCombine 𝔽q β i_ℓ (s + 1)
      (destIdx := destIdx) (h_destIdx := by simp [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).2
    let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    Δ₀(affineLineEvaluation (F := L)
      (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new,
      (C_dest ^⋈ (Fin (2^s)))) ≤
    Code.uniqueDecodingRadius (C := C_dest) := by
  classical
  intro i_ℓ U U_even U_odd C_dest
  have h_midIdx_le_ℓ : midIdx.val ≤ ℓ := by omega
  let fold_1_f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i (destIdx := midIdx) (h_destIdx := h_midIdx)
    (h_destIdx_le := by omega) f_i r_new
  by_cases hs : s = 0
  · subst hs
    have h_midIdx_eq_destIdx : midIdx = destIdx := Fin.eq_of_val_eq (by omega)
    have h_udr_close : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        midIdx  fold_1_f := by
      rw [←fiberwiseClose_steps_zero_iff_uniqueDecodingClose]
      exact h_fw_close
    rw [uniqueDecodingClose_iff_dist_le_uniqueDecodingRadius 𝔽q β
      (h_i := h_midIdx_le_ℓ)] at h_udr_close
    subst h_midIdx_eq_destIdx
    change Δ₀(affineLineEvaluation (F := L)
      (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new,
      interleavedCodeSet (κ := Fin (2 ^ 0)) C_dest) ≤
      Code.uniqueDecodingRadius (C := C_dest)
    rw [distFromCode_interleavedCodeSet_fin_one]
    suffices h_eq : (fun y => affineLineEvaluation
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
        (0 : Fin (2 ^ 0))) =
        fold_1_f by
      rw [h_eq]; exact h_udr_close
    have h_rhs : fold_1_f = multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
      have h_rhs := fold_eq_multilinearCombine_preTensorCombine 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_ℓ)
        (destIdx := midIdx) (h_destIdx := by simp [i_ℓ]; omega)
        (h_destIdx_le := h_midIdx_le_ℓ) (f_i := f_i) (r_new := r_new)
      simp only [fold_1_f, i_ℓ] at h_rhs ⊢
      exact h_rhs
    have h_affine_eq_mc :
        (fun y => affineLineEvaluation
          (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
          (0 : Fin (2 ^ 0))) =
        multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
      ext y
      change (1 - r_new) * U 0 y + r_new * U 1 y = multilinearCombine U (fun _ => r_new) y
      simp [multilinearCombine, multilinearWeight]
    have h_fn_eq : (fun y => affineLineEvaluation
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
        (0 : Fin (2 ^ 0))) = fold_1_f := by
      rw [h_affine_eq_mc, h_rhs]
    rw [h_fn_eq]
  · have h_midIdx_lt_ℓ : midIdx.val < ℓ := by omega
    let midIdx_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    have : NeZero s := ⟨hs⟩
    have h_joint := preTensorCombine_jointProximityNat_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_ℓ) (steps := s)
      (h_destIdx := by simp only [midIdx_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := fold_1_f)
      (h_close := h_fw_close)
    have h_eq := preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i_ℓ) (steps := s)
      (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by simp only [i_ℓ]; omega)
      (h_destIdx := by simp only [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := f_i) (r_new := r_new)
    have h_eq' :
        interleaveWordStack
            (preTensorCombine 𝔽q β
              (i := ⟨midIdx.val, h_midIdx_lt_ℓ⟩) (steps := s)
              (destIdx := destIdx)
              (h_destIdx := by simp; omega)
              (h_destIdx_le := h_destIdx_le) fold_1_f) =
          affineLineEvaluation (F := L)
            (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new := by
      have h_eq' := h_eq
      simp only [U_even, U_odd] at h_eq' ⊢
      exact h_eq'
    unfold jointProximityNat at h_joint
    rw [← h_eq']
    exact h_joint

omit hdiv in
omit [DecidableEq 𝔽q] in
omit [NeZero ℓ] in
omit [NeZero ϑ] in
/-- The per-challenge bound on the incremental folding bad event when the block's oracle is not
fiberwise close. Write `fₖ` for its fold at the fixed prefix of `k` challenges and `U` for the
tensor-combine stack of `fₖ` over the remaining `ϑ - k` folds.

If `fₖ` is already fiberwise close, the event holds at `k` and there is nothing to bound.
Otherwise `U` is far from the interleaved destination code
(`preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose`), so the pair of its even and
odd rows is far as well (`jointProximityNat_of_jointProximityNat₂_splitEvenOdd`). The stack of
the next fold is the affine line through that pair at the fresh challenge
(`preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd`), and it is close whenever the
next fold is fiberwise close (`preTensorCombine_jointProximityNat_of_fiberwiseClose`); the
affine-line proximity gap (`prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂`)
bounds that probability by `|S⁽ⁱ⁺ᶿ⁾| / |L|`. -/
lemma prob_incrementalFoldingBadEvent_fresh_le_of_not_fiberwiseClose
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_far : ¬ FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr{ let r_new ← $ᵗ L }[
      ¬ IncrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      IncrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ)
        (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  let : CharP L 2 := charP_two_of_card_eq_two 𝔽q L
  classical
  dsimp only [IncrementalFoldingBadEvent]
  simp only [h_block_far, ↓reduceDIte]
  let fold_k_f := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_block_start) (r_challenges := r_prefix)
  let Ek_close := FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := midIdx_i) (steps := ϑ - k) (h_destIdx := by omega)
    (h_destIdx_le := h_destIdx_le) (f := fold_k_f)
  by_cases h_Ek_close : Ek_close
  · apply le_trans (prEvent_mono ($ᵗ L) _ _ (fun r_new h => h.1))
    have : Pr{ let r_new ← $ᵗ L }[¬Ek_close] = 0 := by
      rw [SampleableType.prEvent_uniformSample]
      simp only [not_not.mpr h_Ek_close, Finset.filter_false, card_empty, CharP.cast_eq_zero,
        ENNReal.zero_div]
    rw [this]; exact bot_le
  · apply le_trans (prEvent_mono ($ᵗ L) _ _ (fun r_new h => h.2))
    have h_midIdx_i_lt_ℓ : midIdx_i.val < ℓ := by omega
    let s := ϑ - k - 1
    have h_steps_eq : ϑ - k = s + 1 := by omega
    let S_dest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let C_dest : Set (S_dest → L) :=
      code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    let e_prox := Code.uniqueDecodingRadius (C := C_dest)
    let i_ℓ : Fin ℓ := ⟨midIdx_i.val, h_midIdx_i_lt_ℓ⟩
    let U := preTensorCombine 𝔽q β i_ℓ (s + 1)
      (destIdx := destIdx)
      (h_destIdx := by simp [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      fold_k_f
    have h_U_far : ¬jointProximityNat (C := C_dest) (u := U)
        (e := e_prox) := by
      apply preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i_ℓ) (steps := s + 1)
        (h_destIdx := by simp [i_ℓ]; omega)
        (h_destIdx_le := h_destIdx_le)
        (f_i := fold_k_f)
        (h_far := by convert h_Ek_close using 2; omega)
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).2
    let u_even := interleaveWordStack U_even
    let u_odd := interleaveWordStack U_odd
    have h_pair_far : ¬ jointProximityNat₂
        (A := InterleavedSymbol L (Fin (2^s)))
        (C := (C_dest ^⋈ (Fin (2^s))))
        (u₀ := u_even) (u₁ := u_odd) (e := e_prox) :=
      fun h_close => h_U_far
        (jointProximityNat_of_jointProximityNat₂_splitEvenOdd C_dest U e_prox h_close)
    have h_affine_bound :
        Pr{let r ← $ᵗ L}[
          Δ₀(affineLineEvaluation (F := L) u_even u_odd r,
            (C_dest ^⋈ (Fin (2^s)))) ≤ e_prox]
        ≤ (Fintype.card S_dest : ℝ≥0) / (Fintype.card L) :=
      prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂
        𝔽q β h_destIdx_le
        (e := e_prox) (he := le_refl _) (h_far := h_pair_far)
    apply le_trans _ h_affine_bound
    apply prEvent_mono ($ᵗ L) _ _
    intro r_new h_fw_close
    exact distFromCode_affineLineEvaluation_le_of_fiberwiseClose_fold 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_i) (h_i_lt_ℓ := h_midIdx_i_lt_ℓ) (s := s)
      (midIdx := midIdx_i_succ) (destIdx := destIdx)
      (h_midIdx := by omega)
      (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := fold_k_f) (r_new := r_new)
      (h_fw_close := by
        rw [iteratedFold_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          block_start_idx (steps := k)
          (h_midIdx := h_midIdx_i) (h_destIdx := h_midIdx_i_succ)
          (h_destIdx_le := by omega)
          f_block_start (Fin.snoc r_prefix r_new)] at h_fw_close
        simp only [Fin.init_snoc, Fin.snoc_last] at h_fw_close
        convert h_fw_close using 1)

omit [DecidableEq 𝔽q] hdiv in
omit [NeZero ℓ] in
omit [NeZero ϑ] in
/-- For a block starting at `block_start_idx`, an oracle `f_block_start` and a fixed prefix of
`k < ϑ` challenges, the probability over a fresh uniform challenge `r_new` that the incremental
folding bad event holds after `k + 1` challenges but not after `k` is at most
`|S⁽ⁱ⁺ᶿ⁾| / |L|`. -/
lemma prob_incrementalFoldingBadEvent_fresh_le
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr{ let r_new ← $ᵗ L }[
      ¬ IncrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      IncrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ)
        (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  classical
  by_cases h_block_close : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f_block_start)
  · exact prob_incrementalFoldingBadEvent_fresh_le_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx)
      (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i)
      (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_close := h_block_close)
  · exact prob_incrementalFoldingBadEvent_fresh_le_of_not_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx)
      (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i)
      (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_far := h_block_close)

end

end Binius.BinaryBasefold
