/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.FloorTransfer

/-!
# Normalizing the complete partition source integral

This layer isolates the deterministic rescaling from the ordered-simplex moment.
The source comparison uses the entire simplex and preserves the factor `1/2`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory SimplexIntegration

/-- A lower level comparison survives the positive-part square rescaling. -/
theorem partition_square_rescale {level rate radius degree logarithm total : ℝ}
    (hrate : 0 < rate) (hradius : 0 < radius) (hdegree : 0 < degree)
    (hlevel : rate * radius / degree * logarithm ≤ level) :
    (rate * radius / degree) ^ 2 * (max (logarithm - degree * total / radius) 0) ^ 2 ≤
      (max (level - rate * total) 0) ^ 2 := by
  have hscale : 0 < rate * radius / degree := by positivity
  have hid : rate * radius / degree * (logarithm - degree * total / radius) =
      rate * radius / degree * logarithm - rate * total := by field_simp
  rw [← mul_pow, mul_max_of_nonneg _ _ hscale.le, mul_zero, hid]
  exact pow_le_pow_left₀ (by positivity) (max_le_max_right _ (by linarith)) 2

/-- A whole-simplex moment lower bound gives its correctly scaled source integral bound. -/
theorem partition_integral_ge_normalized_moment (d budget : ℕ) (level rate logarithm : ℝ)
    (hd : 0 < d) (hbudget : 0 < budget) (hrate : 0 < rate)
    (hlevel : rate * budget / d * logarithm ≤ level) :
    (rate * budget / d) ^ 2 *
      (∫ point in weightedSimplex d budget,
        (max (logarithm - (d : ℝ) * weightedRadius point / budget) 0) ^ 2) ≤
      ∫ point in weightedSimplex d budget,
        (max (level - rate * ∑ index, point index) 0) ^ 2 := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on
  · apply Continuous.integrableOn_weightedSimplex (hW := Nat.cast_nonneg budget)
    unfold weightedRadius
    fun_prop
  · apply Continuous.integrableOn_weightedSimplex (hW := Nat.cast_nonneg budget)
    fun_prop
  · exact (isCompact_weightedSimplex d (Nat.cast_nonneg budget)).isClosed.measurableSet
  · intro point _
    exact partition_square_rescale hrate (Nat.cast_pos.mpr hbudget) (Nat.cast_pos.mpr hd) hlevel

/-- Undoing normalized expectation multiplies by exactly the weighted simplex volume. -/
theorem partition_integral_eq_volume_mul_expectation (d : ℕ) {radius : ℝ}
    (hradius : 0 < radius) (integrand : (Fin d → ℝ) → ℝ) :
    (∫ point in weightedSimplex d radius, integrand point) =
      (radius ^ d / (d.factorial : ℝ) ^ 2) * weightedSimplexExpectation d radius integrand := by
  unfold weightedSimplexExpectation
  rw [setAverage_eq, smul_eq_mul, volume_weightedSimplex d hradius.le]
  have hvolume : (radius ^ d / (d.factorial : ℝ) ^ 2) ≠ 0 := by positivity
  rw [← mul_assoc, mul_inv_cancel₀ hvolume, one_mul]

/-- The exact `27/20` source coefficient is half the strict `27/10` moment bound. -/
theorem partitionSupport_dimension_gt_moment {F : Type*} [Field F]
    {D d n m A budget : ℕ} {rate agreement logarithm : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hn : 0 < n) (hbudget : 0 < budget) (hrate : 0 < rate)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A)
    (hlevel : rate * budget / d * logarithm ≤ m * agreement)
    (hmoment : (27 / 10 : ℝ) < weightedSimplexExpectation d budget
      (fun point ↦ (max (logarithm - (d : ℝ) * weightedRadius point / budget) 0) ^ 2)) :
    (27 / 20 : ℝ) * n * rate * ((budget : ℝ) / d) ^ 2 *
      ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) <
        (Module.finrank F (partitionSupportSpace F D d budget (m * A : ℕ) hD) : ℝ) := by
  have hscale : 0 < (n : ℝ) / (2 * rate) * (rate * budget / d) ^ 2 *
      ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by positivity
  have hstrict := mul_lt_mul_of_pos_left hmoment hscale
  have hintegral := partition_integral_ge_normalized_moment d budget
    ((m : ℝ) * agreement) rate logarithm hd hbudget hrate hlevel
  rw [partition_integral_eq_volume_mul_expectation d (Nat.cast_pos.mpr hbudget)] at hintegral
  have hsource := (mul_le_mul_of_nonneg_left hintegral
    (show 0 ≤ (n : ℝ) / (2 * rate) by positivity)).trans
      (partitionSupport_dimension_ge_rate_integral (F := F) hD hn hrate hupper hlower)
  have hnormalize : (n : ℝ) / (2 * rate) * (rate * budget / d) ^ 2 *
      ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) * (27 / 10) =
      (27 / 20 : ℝ) * n * rate * ((budget : ℝ) / d) ^ 2 *
        ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hnormalize] at hstrict
  exact hstrict.trans_le (by simpa only [mul_assoc] using hsource)

end ReedSolomon.HiddenDerivative
