/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateRounding

/-!
# Exact first-order rank rounding on the upper derivative branch

For derivative ratio at least `1/2`, the exact all-`M` local-rank count is linear in the rounded
cap.  This removes the cubic-envelope loss which is harmless on the clean branch but macroscopic
for the stationary low-rate optimizer.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

private def allMLinearSum (x : ℝ) : ℝ := x * (x - 1) / 2

private def allMSquareSum (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem allM_sum_range_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = allMLinearSum n := by
  induction n with
  | zero => simp [allMLinearSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [allMLinearSum]
      push_cast
      ring

private theorem allM_sum_range_sq_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = allMSquareSum n := by
  induction n with
  | zero => simp [allMSquareSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [allMSquareSum]
      push_cast
      ring

private theorem allM_rank_correction_le_ambient {m M s : ℕ} (hs : s < m) :
    (2 * s + 1 - m) * (s + M + 1 - m) ≤ (s + 1) * (M + 1) := by
  apply Nat.mul_le_mul <;> omega

private theorem firstOrderRateRankCount_eq_upperBranchFormula {m M : ℕ}
    (hhalf : m ≤ 2 * M + 1) :
    (firstOrderRateRankCount m M : ℝ) =
      (M + 1) * (allMLinearSum m + m) -
        (2 * (allMSquareSum m - allMSquareSum ((m / 2 : ℕ) : ℝ)) +
          (2 * M + 3 - 3 * m) *
            (allMLinearSum m - allMLinearSum ((m / 2 : ℕ) : ℝ)) +
          ((m : ℝ) - ((m / 2 : ℕ) : ℝ)) * (1 - m) * (M + 1 - m)) := by
  let q := m / 2
  have hqm : q ≤ m := Nat.div_le_self _ _
  rw [firstOrderRateRankCount, Nat.cast_sum]
  have hrank :
      (∑ s ∈ Finset.range m,
          (((s + 1) * (M + 1) -
            (2 * s + 1 - m) * (s + M + 1 - m) : ℕ) : ℝ)) =
        (∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) -
          ∑ s ∈ Finset.range m,
            (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Nat.cast_sub (allM_rank_correction_le_ambient (Finset.mem_range.mp hs))]
    push_cast
    rfl
  rw [hrank]
  have hcorrection :
      (∑ s ∈ Finset.range m,
          (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ))) =
        ∑ s ∈ Finset.Ico q m,
          (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m) := by
    rw [← Finset.sum_range_add_sum_Ico _ hqm]
    have hzero :
        (∑ s ∈ Finset.range q,
          (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ))) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hslt : 2 * s + 1 ≤ m := by
        have : s < q := Finset.mem_range.mp hs
        dsimp only [q] at this
        omega
      rw [Nat.sub_eq_zero_of_le hslt]
      simp
    rw [hzero, zero_add]
    apply Finset.sum_congr rfl
    intro s hs
    have hsq : q ≤ s := (Finset.mem_Ico.mp hs).1
    have hsm : s < m := (Finset.mem_Ico.mp hs).2
    have hfirst : m ≤ 2 * s + 1 := by
      dsimp only [q] at hsq
      omega
    have hsecond : m ≤ s + M + 1 := by
      dsimp only [q] at hsq
      omega
    rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond]
  rw [hcorrection]
  have hamb (n : ℕ) :
      (∑ s ∈ Finset.range n, ((s + 1 : ℕ) : ℝ) * (M + 1)) =
        (M + 1) * (allMLinearSum n + n) := by
    calc
      _ = (M + 1 : ℝ) * ((∑ s ∈ Finset.range n, (s : ℝ)) + n) := by
        push_cast
        ring_nf
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [allM_sum_range_cast]
  have hcorrectionFormula (n : ℕ) :
      (∑ s ∈ Finset.range n,
        (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) =
        2 * allMSquareSum n + (2 * M + 3 - 3 * m) * allMLinearSum n +
          n * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ s ∈ Finset.range n,
          (2 * (s : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * s +
            (1 - m) * (M + 1 - m)) := by
        apply Finset.sum_congr rfl
        intro s _
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, allM_sum_range_cast,
          allM_sum_range_sq_cast]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [Finset.sum_Ico_eq_sub _ hqm, hamb, hcorrectionFormula, hcorrectionFormula]
  dsimp only [q]
  simp only [allMLinearSum, allMSquareSum]
  ring

private def allMRankRoundingModel (u v : ℝ) : ℝ :=
  (u + v) * ((1 - v) / 2 + v) -
    (2 * ((1 - v) * (2 - v) / 6 -
        (1 - u) * (1 - u - v) * (2 * (1 - u) - v) / 6) +
      (2 * u + 3 * v - 3) *
        ((1 - v) / 2 - (1 - u) * (1 - u - v) / 2) +
      u * (v - 1) * (u + v - 1))

private theorem allMRankRoundingModel_le
    {u v beta : ℝ} (hu0 : 0 ≤ u) (hub : u ≤ beta) (hbu : beta ≤ u + v)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hb1 : beta ≤ 3 / 4) :
    allMRankRoundingModel u v ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v := by
  unfold allMRankRoundingModel
  have hu34 : u ≤ 3 / 4 := hub.trans hb1
  have hq : 0 ≤ 1 / 2 - (beta + u) / 2 +
      (beta ^ 2 + beta * u + u ^ 2) / 3 := by
    nlinarith [sq_nonneg (beta - u), sq_nonneg (beta + u - 1)]
  have hP : u / 2 - u ^ 2 / 2 + u ^ 3 / 3 ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 := by
    have hdiff :
      (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3) -
          (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) =
        (beta - u) * (1 / 2 - (beta + u) / 2 +
          (beta ^ 2 + beta * u + u ^ 2) / 3) := by ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hub) hq]
  have hvSq : v ^ 2 ≤ v := by
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have huSq : u ^ 2 ≤ (9 / 16 : ℝ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hu34)
      (add_nonneg hu0 (by norm_num : (0 : ℝ) ≤ 3 / 4))
    nlinarith
  have huSqV : u ^ 2 * v ≤ (9 / 16 : ℝ) * v :=
    mul_le_mul_of_nonneg_right huSq hv0
  have huVSq : u * v ^ 2 ≤ (3 / 4 : ℝ) * v := by
    calc
      u * v ^ 2 ≤ (3 / 4 : ℝ) * v ^ 2 :=
        mul_le_mul_of_nonneg_right hu34 (sq_nonneg v)
      _ ≤ (3 / 4 : ℝ) * v := mul_le_mul_of_nonneg_left hvSq (by norm_num)
  ring_nf at ⊢
  nlinarith

private theorem firstOrderRankCubicUpperCount_normalized_eq_allMModel {m M : ℕ}
    (hm : 0 < m) (hM : M ≤ m) :
    firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 =
      allMRankRoundingModel ((M : ℝ) / m) ((m : ℝ)⁻¹) := by
  have hamb (q : ℕ) :
      (∑ s ∈ Finset.range q, ((s + 1 : ℕ) : ℝ) * (M + 1)) =
        (M + 1) * (allMLinearSum q + q) := by
    calc
      _ = (M + 1 : ℝ) * ((∑ s ∈ Finset.range q, (s : ℝ)) + q) := by
        push_cast
        ring_nf
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [allM_sum_range_cast]
  have hcorrection (q : ℕ) :
      (∑ s ∈ Finset.range q,
        (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) =
        2 * allMSquareSum q + (2 * M + 3 - 3 * m) * allMLinearSum q +
          q * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ s ∈ Finset.range q,
          (2 * (s : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * s +
            (1 - m) * (M + 1 - m)) := by
        apply Finset.sum_congr rfl
        intro s _
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, allM_sum_range_cast,
          allM_sum_range_sq_cast]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [firstOrderRankCubicUpperCount,
    Finset.sum_Ico_eq_sub _ (Nat.sub_le m M), hamb, hcorrection, hcorrection]
  rw [Nat.cast_sub hM]
  simp only [allMLinearSum, allMSquareSum, allMRankRoundingModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

private theorem firstOrderRateRankCount_floor_le_density_add_three_mul_sq_lower
    {beta : ℝ} (hbeta0 : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) (m : ℕ) :
    (firstOrderRateRankCount m (Nat.floor (beta * m)) : ℝ) ≤
      (m : ℝ) ^ 3 * firstOrderRankDensity beta + 3 * (m : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · subst m
    simp [firstOrderRateRankCount]
  let M := Nat.floor (beta * m)
  let u : ℝ := M / m
  let v : ℝ := (m : ℝ)⁻¹
  have hmNat : 0 < m := Nat.pos_of_ne_zero hm
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hMReal : (M : ℝ) ≤ beta * m := by
    dsimp only [M]
    exact Nat.floor_le (mul_nonneg hbeta0 hmReal.le)
  have hMlt : beta * m < (M : ℝ) + 1 := by
    dsimp only [M]
    exact Nat.lt_floor_add_one _
  have hMNat : M ≤ m := by
    have hreal : (M : ℝ) ≤ m := hMReal.trans <| by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbetaHalf) hmReal.le]
    exact_mod_cast hreal
  have hu0 : 0 ≤ u := by unfold u; positivity
  have hub : u ≤ beta := by
    unfold u
    exact (div_le_iff₀ hmReal).2 (by simpa [mul_comm] using hMReal)
  have hbu : beta ≤ u + v := by
    unfold u v
    rw [show (M : ℝ) / m + (m : ℝ)⁻¹ = ((M : ℝ) + 1) / m by
      field_simp [ne_of_gt hmReal]]
    exact (le_div_iff₀ hmReal).2 (by linarith)
  have hv0 : 0 ≤ v := by unfold v; positivity
  have hv1 : v ≤ 1 := by
    unfold v
    rw [inv_le_one₀ hmReal]
    exact_mod_cast hmNat
  have hmodel := allMRankRoundingModel_le hu0 hub hbu hv0 hv1
    (hbetaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4))
  have hrankDensity : firstOrderRankDensity beta =
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 := by
    rw [firstOrderRankDensity, if_pos hbetaHalf]
  have hnormalized : firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 ≤
      firstOrderRankDensity beta + 3 / m := by
    rw [firstOrderRankCubicUpperCount_normalized_eq_allMModel hmNat hMNat,
      hrankDensity]
    dsimp only [u, v] at hmodel ⊢
    simpa [div_eq_mul_inv] using hmodel
  have hmCube : 0 < (m : ℝ) ^ 3 := pow_pos hmReal 3
  have hupper : firstOrderRankCubicUpperCount m M ≤
      (m : ℝ) ^ 3 * (firstOrderRankDensity beta + 3 / m) := by
    simpa [mul_comm] using (div_le_iff₀ hmCube).mp hnormalized
  have hscale : (m : ℝ) ^ 3 * (firstOrderRankDensity beta + 3 / m) =
      (m : ℝ) ^ 3 * firstOrderRankDensity beta + 3 * (m : ℝ) ^ 2 := by
    field_simp [ne_of_gt hmReal]
  calc
    (firstOrderRateRankCount m (Nat.floor (beta * m)) : ℝ) ≤
        firstOrderRankCubicUpperCount m M := by
      simpa only [M] using firstOrderRateRankCount_le_cubicUpperCount m M
    _ ≤ (m : ℝ) ^ 3 * (firstOrderRankDensity beta + 3 / m) := hupper
    _ = _ := hscale

/-- On the upper rank branch, exact floor rounding loses at most the manuscript coefficient
`(2*beta+3)m²`. -/
theorem firstOrderRateRankCount_floor_le_density_add_rounding_upper
    {beta : ℝ} (hbeta : 1 / 2 ≤ beta) (m : ℕ) :
    (firstOrderRateRankCount m (Nat.floor (beta * m)) : ℝ) ≤
      (m : ℝ) ^ 3 * firstOrderRankDensity beta +
        (2 * beta + 3) * (m : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · subst m
    simp [firstOrderRateRankCount]
  let M := Nat.floor (beta * m)
  have hmNat : 0 < m := Nat.pos_of_ne_zero hm
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hbeta0 : 0 ≤ beta := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hbeta
  have hMle : (M : ℝ) ≤ beta * m := by
    dsimp only [M]
    exact Nat.floor_le (mul_nonneg hbeta0 hmReal.le)
  have hMlt : beta * m < (M : ℝ) + 1 := by
    dsimp only [M]
    exact Nat.lt_floor_add_one _
  have hhalf : m ≤ 2 * M + 1 := by
    have hreal : (m : ℝ) < 2 * ((M : ℝ) + 1) := by
      nlinarith
    have hnat : m < 2 * (M + 1) := by exact_mod_cast hreal
    omega
  rw [show Nat.floor (beta * m) = M by rfl,
    firstOrderRateRankCount_eq_upperBranchFormula hhalf]
  have hrankDensity : firstOrderRankDensity beta = beta / 4 + 1 / 24 := by
    rw [firstOrderRankDensity]
    split_ifs with h
    · have heq : beta = 1 / 2 := le_antisymm h hbeta
      subst beta
      norm_num
    · rfl
  rw [hrankDensity]
  obtain ⟨h, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hdiv : 2 * h / 2 = h := by omega
    simp only [hdiv, allMLinearSum, allMSquareSum]
    push_cast at hMle ⊢
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have hhOne : (1 : ℝ) ≤ h := by
      exact_mod_cast (show 1 ≤ h by omega)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hmul1 := mul_le_mul_of_nonneg_right hMle hh
    have hmul := mul_le_mul_of_nonneg_right hMle (sq_nonneg (h : ℝ))
    ring_nf at ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hhOne) hh,
      mul_nonneg hM0 hh]
  · have hdiv : (2 * h + 1) / 2 = h := by omega
    simp only [hdiv, allMLinearSum, allMSquareSum]
    push_cast at hMle ⊢
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hMle (sq_nonneg ((2 : ℝ) * h + 1))
    nlinarith [sq_nonneg (beta : ℝ), sq_nonneg ((M : ℝ) - beta * (2 * h + 1)),
      mul_nonneg hM0 hh]

/-- Exact all-`M` floor rounding against the piecewise rank density, uniformly on both branches. -/
theorem firstOrderRateRankCount_floor_le_density_add_rounding
    {beta : ℝ} (hbeta0 : 0 ≤ beta) (m : ℕ) :
    (firstOrderRateRankCount m (Nat.floor (beta * m)) : ℝ) ≤
      (m : ℝ) ^ 3 * firstOrderRankDensity beta +
        (2 * beta + 3) * (m : ℝ) ^ 2 := by
  by_cases hbetaHalf : beta ≤ 1 / 2
  · have h := firstOrderRateRankCount_floor_le_density_add_three_mul_sq_lower
      hbeta0 hbetaHalf m
    exact h.trans (by
      have hmSq : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hbeta0 hmSq])
  · exact firstOrderRateRankCount_floor_le_density_add_rounding_upper
      (le_of_not_ge hbetaHalf) m

end

end ReedSolomon.HiddenDerivative
