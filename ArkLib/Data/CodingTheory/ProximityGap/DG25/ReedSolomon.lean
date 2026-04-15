/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.DG25.MainResults

/-!
# DG25 Reed-Solomon Corollaries

This module specializes the DG25 proximity-gap framework to Reed-Solomon codes and proves
the resulting affine-line and tensor-gap corollaries.
-/

noncomputable section

open Code LinearCode InterleavedCode ReedSolomonCode ProximityGap ProbabilityTheory Filter
open NNReal Finset Function
open scoped BigOperators LinearCode ProbabilityTheory
open Real

universe u v w k l
variable {κ : Type k} {ι : Type l} [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq κ]
variable {F : Type v} [Semiring F] [Fintype F]
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A]
section RSCode_Corollaries
variable {n k : ℕ} {A : Type} [NeZero n] [NeZero k] (hk : k ≤ n)
  {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq F] {α : ι ↪ A}
    (h_deg_le_length : k ≤ Fintype.card ι)
  {domain : (Fin n) ↪ A} [DecidableEq A] [Field A] [Fintype A]

/-
Theorem 2.2 (Ben-Sasson, et al. [Ben+23, Thm. 4.1]). For each `e ∈ {0, ..., ⌊(d-1)/2⌋}`,
`RS_{F, S}[k, n]` exhibits proximity gaps for affine lines with respect to the
proximity parameter `e` and the false witness bound `ε := n`.
-/
theorem ReedSolomon_ProximityGapAffineLines_UniqueDecoding [Nontrivial (ReedSolomon.code α k)]
    (hk : k ≤ Fintype.card ι) :
    ∀ e ≤ (Code.uniqueDecodingRadius (C := (ReedSolomon.code α k : Set (ι → A)))),
      e_ε_correlatedAgreementAffineLinesNat (F := A) (A := A) (ι := ι)
        (C := (ReedSolomon.code α k : Set (ι → A)))
        (e := e) (ε := Fintype.card (ι)) := by
  set n := Fintype.card ι
  intro e he_unique_decoding_radius u₀ u₁ h_prob_affine_line_close_gt
  -- Apply theorem 4.1 (BCIKS20)
  let δ : ℝ≥0 := (e : ℝ≥0) / (Fintype.card (ι) : ℝ≥0)
  have h_δ_mul_n_eq_e: Nat.floor (δ * Fintype.card (ι)) = e := by
    dsimp only [Fin.isValue, δ]
    rw [div_mul]
    rw [div_self (h := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
      not_false_eq_true]), div_one]
    simp only [Nat.floor_natCast]
  set CRS := ReedSolomon.code α k
  have h_dist_RS := ReedSolomonCode.dist_eq' (F := A) (α := α)
    (n := k) (ι := ι) (h := hk)
  have h_dist_CRS : ‖(CRS : Set (ι → A))‖₀ = n - k + 1 := h_dist_RS
  have he_le_NNReal : (e : ℝ≥0)
    ≤ (((Code.dist (R := A) (n := ι) (C := CRS)) - 1) : ℝ≥0) / 2 := by
    rw [uniqueDecodingRadius_eq_floor_div_2] at he_unique_decoding_radius
    rw [Nat.le_floor_iff (ha := by simp only [zero_le])] at he_unique_decoding_radius
    exact he_unique_decoding_radius
  have h_δ_within_rel_URD : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := A)
    (C := ReedSolomon.code α k) := by
    dsimp [δ, Code.relativeUniqueDecodingRadius]
    rw [div_le_iff₀ (hc := by simp only [Nat.cast_pos, Fintype.zero_lt_card])]
    rw [div_mul]
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, div_self, div_one]
    exact he_le_NNReal
  have h_rewrite_prob : Pr_{let z ← $ᵖ A}[Δ₀((1 - z) • u₀ + z • u₁, CRS) ≤ e]
    = Pr_{let z ← $ᵖ A}[Δ₀(u₀ + z • (u₁ - u₀), CRS) ≤ e] := by
    congr  -- Peel away the Pr_{...} wrapper
    funext z
    congr! 1 -- Focus on the term inside Δ₀
    -- Apply the algebra derived above
    rw [sub_smul, one_smul, smul_sub]
    abel_nf
  have h_correlated_agreement := RS_correlatedAgreement_affineLines_uniqueDecodingRegime (deg := k)
    (domain := α) (ι := ι) (F := A) (δ := δ) (hδ := by exact h_δ_within_rel_URD)
  unfold affineLineEvaluation at h_prob_affine_line_close_gt
  rw [h_rewrite_prob] at h_prob_affine_line_close_gt
  -- now we can apply RS_correlatedAgreement_affineLines_uniqueDecodingRegime
  let uShifted := finMapTwoWords u₀ (u₁ - u₀)
  have h_errorBound_UDR_eq : (errorBound δ k α)
    = (Fintype.card (ι) : ℝ≥0) / (Fintype.card A : ℝ≥0) := by
    unfold errorBound
    have h_δ_mem : δ ∈ Set.Icc 0 (((1 : ℝ≥0) - (rate (ReedSolomon.code α k))) / 2) := by
      simp only [Set.mem_Icc, zero_le, true_and]
      rw [rateOfLinearCode_eq_div' (h := by omega)]
      simp only [NNRat.cast_div, NNRat.cast_natCast]
      rw [←ReedSolomonCode.relativeUniqueDecodingRadius_RS_eq' (F := A)
        (ι := ι) (h := by omega)]
      rw [dist_le_UDR_iff_relDist_le_relUDR] at he_unique_decoding_radius
      exact he_unique_decoding_radius
    simp only [h_δ_mem, ↓reduceIte]
  rw [h_errorBound_UDR_eq] at h_correlated_agreement
  -- convert h_correlated_agreement into absolute distance bound
  unfold  δ_ε_correlatedAgreementAffineLines at h_correlated_agreement
  simp_rw [relDistFromCode_le_iff_distFromCode_le] at h_correlated_agreement
  let h_u₀_and_u₁_sub_u₀_CA := h_correlated_agreement uShifted (by
    rw [h_δ_mul_n_eq_e]
    simp only [Fin.isValue, bind_pure_comp, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
      not_false_eq_true, ENNReal.coe_div, ENNReal.coe_natCast, gt_iff_lt]
    simp only [ENNReal.coe_natCast] at h_prob_affine_line_close_gt
    exact h_prob_affine_line_close_gt
  )
  rw [jointAgreement_iff_jointProximity] at h_u₀_and_u₁_sub_u₀_CA
  -- we have jointProximity₂ (u₀ := u₀) (u₁ := u₁ - u₀) (δ := δ) at h_u₀_and_u₁_sub_u₀_CA
  have h_jointProximity₂ : jointProximity₂ (C := CRS) (u₀ := u₀) (u₁ := u₁ - u₀) (δ := δ) := by
    exact h_u₀_and_u₁_sub_u₀_CA
  letI : Nontrivial (CRS) := by infer_instance
  let jointProximity₂_u₀_u₁ := jointProximity₂_affineShift_implies_jointProximity₂ (ι := ι)
    (MC := CRS) (u₀ := u₀) (u₁ := u₁) (δ := δ) (h_jointProximity₂)
  unfold jointProximity₂ jointProximity at jointProximity₂_u₀_u₁
  rw [relDistFromCode_le_iff_distFromCode_le] at jointProximity₂_u₀_u₁
  rw [h_δ_mul_n_eq_e] at jointProximity₂_u₀_u₁
  exact jointProximity₂_u₀_u₁

/-- **Corollary 3.7**: RS Codes have Tensor-Style Proximity Gaps (Unique Decoding)
Example 4.1 shows that ε=n is tight for RS codes (Ben+23 Thm 4.1 is sharp). -/
theorem reedSolomon_multilinearCorrelatedAgreement_Nat [Nontrivial (ReedSolomon.code α k)]
    {e : ℕ} (hk : k ≤ Fintype.card ι)
    (he : e ≤ (Code.uniqueDecodingRadius (C := (ReedSolomon.code α k : Set (ι → A))))) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := A) (A := A)
      (ι := ι) (C := (ReedSolomon.code α k : Set (ι → A)))
      (ϑ := ϑ) (e := e) (ε := Fintype.card ι) := by
    set n := Fintype.card ι
    intro ϑ hϑ_gt_0 u h_prob_tensor_gt
    set C_RS: ModuleCode ι A A := ReedSolomon.code α k
    have h_dist_RS := ReedSolomonCode.dist_eq'  (F := A) (α := α)
      (n := k) (ι := ι) (h := hk)
    have h_dist_CRS : ‖(C_RS : Set (ι → A))‖₀ = n - k + 1 := h_dist_RS
    -- 1. Apply ReedSolomon_ProximityGapAffineLines_UniqueDecoding (BCIKS20 Thm 4.1)
    have h_fincard_n : Fintype.card (ι) = n := by rfl
    have h_affine_gap_base : e_ε_correlatedAgreementAffineLinesNat (F := A) (A := A) (ι := ι)
      (C := C_RS) (e := e) (ε := n) := by
      let res := ReedSolomon_ProximityGapAffineLines_UniqueDecoding (A := A)
        (hk := by omega) (e := e) he
      rw [h_fincard_n] at res
      exact res
    -- 2. Check condition ε ≥ e + 1 for Theorem 3.1
    have h_eps_ge_e1 : n ≥ e + 1 := by
      simp only [uniqueDecodingRadius] at he
      simp_rw [h_dist_CRS] at he
      simp only [add_tsub_cancel_right] at he
      rw [ge_iff_le];
      apply Nat.le_of_lt_succ;
      have h_lt : e + 1 < (n - k) / 2 + 1 + 1 := by omega
      have h_le : (n - k) / 2 + 1 ≤ n := by
        exact Nat.sub_div_two_add_one_le n k hk
      omega
    -- 3. Apply Theorem 3.1 inductively (or just state it's needed for Thm 3.6)
    have h_affine_gap_interleaved : ∀ m, (hm: m ≥ 1) →
        letI : Nonempty (Fin m × (ι)) := by
          apply nonempty_prod.mpr
          constructor
          · exact Fin.pos_iff_nonempty.mp hm
          · omega
        e_ε_correlatedAgreementAffineLinesNat
          (F := A) (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := C_RS ^⋈ (Fin m))
          e (Fintype.card (ι)) := by
      intro m hm
      let res := affine_gaps_lifted_to_interleaved_codes (MC := C_RS)
        (F := A) (A := A) (hε := h_eps_ge_e1) (e := e)
        (m := m) (hProximityGapAffineLines := h_affine_gap_base) (he := he)
      rw [h_fincard_n]
      exact res
    -- 4. Apply Theorem 3.6 (AER24)
    let RS_tensor_gap := interleaved_affine_gaps_imply_tensor_gaps
      (MC := C_RS) (h_interleaved_gaps := by
      rw [h_fincard_n] at h_affine_gap_interleaved
      exact h_affine_gap_interleaved) h_affine_gap_base
    exact RS_tensor_gap ϑ hϑ_gt_0 u h_prob_tensor_gt

theorem reedSolomon_multilinearCorrelatedAgreement [Nontrivial (ReedSolomon.code α k)]
    (hk : k ≤ Fintype.card ι) {δ : ℝ≥0} (he : δ ≤ (Code.relativeUniqueDecodingRadius
      (C := (ReedSolomon.code α k : Set (ι → A))))) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) →
      δ_ε_multilinearCorrelatedAgreement (F := A) (A := A) (ι := ι) (ϑ := ϑ) (δ := δ)
      (C := (ReedSolomon.code α k : Set (ι → A)))
      (ε := ((Fintype.card ι) : ℝ≥0) / (Fintype.card A)) := by
  set n := Fintype.card ι
  intro ϑ hϑ_gt_0 u h_prob_u_close_gt
  let e : ℕ := Nat.floor (δ * n)
  have h_δᵣ_close_iff_Δ₀_close : ∀ (r : Fin ϑ → A),
    (δᵣ(multilinearCombine u r, ↑(ReedSolomon.code α k)) ≤ ↑δ)
      ↔ (Δ₀(multilinearCombine u r, ↑(ReedSolomon.code α k)) ≤ e) := by
      intro r
      conv_lhs => rw [relDistFromCode_le_iff_distFromCode_le]
  simp_rw [h_δᵣ_close_iff_Δ₀_close] at h_prob_u_close_gt
  simp only [ENNReal.coe_natCast, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
    not_false_eq_true, ENNReal.coe_div, mul_div] at h_prob_u_close_gt
  letI : Nontrivial (ReedSolomon.code α k) := by infer_instance
  have hCA_Nat_if_then := reedSolomon_multilinearCorrelatedAgreement_Nat (A := A) (ι := ι) (α := α)
    (ϑ := ϑ) (hϑ_gt_0 := hϑ_gt_0) (hk := hk) (e := e) (he := by
    rw [dist_le_UDR_iff_relDist_le_relUDR]
    calc
      _ ≤ δ := by
        simp only [e]; rw [div_le_iff₀ (hc := by
          simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)]
        apply Nat.floor_le;
        exact zero_le (δ * ↑n)
      _ ≤ _ := by exact he
  )
  let h_CA_Nat := hCA_Nat_if_then u (by
    simp only [ENNReal.coe_natCast]
    exact h_prob_u_close_gt
  )
  rw [jointAgreement_iff_jointProximity]
  unfold jointProximity
  rw [relDistFromCode_le_iff_distFromCode_le]
  unfold jointProximityNat at h_CA_Nat
  exact h_CA_Nat

end RSCode_Corollaries

end
