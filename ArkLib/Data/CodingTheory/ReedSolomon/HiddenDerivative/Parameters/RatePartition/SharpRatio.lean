/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Rounding300

/-! # Sharpened finite rate-partition parameters -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- Limiting partition ratio using the sharpened `273/200` coefficient. -/
def sharpRatePartitionGamma (R a : ℝ) (d : ℕ) : ℝ :=
  (273 / 200) * R * (d + 1) / (6 * d : ℝ) ^ (R / a)

/-- Finite sharpened ratio, with the same exact integer radius and rank losses. -/
def sharpRatePartitionFiniteRatio (R a : ℝ) (d m : ℕ) : ℝ :=
  let w := (ratePartitionWeight R a d m : ℝ) / m
  let lam := (d : ℝ) / w
  let S := (d : ℝ) * (d + 1) / 2
  (273 / 200) * R * (d + 1) * Real.exp (-lam * (1 + S / m)) /
    (1 + (d + 1) * lam / m)

theorem sharpRatePartitionGamma_eq_scale (R a : ℝ) (d : ℕ) :
    sharpRatePartitionGamma R a d = (91 / 90 : ℝ) * ratePartitionGamma R a d := by
  unfold sharpRatePartitionGamma ratePartitionGamma
  ring

theorem sharpRatePartitionFiniteRatio_eq_scale (R a : ℝ) (d m : ℕ) :
    sharpRatePartitionFiniteRatio R a d m =
      (91 / 90 : ℝ) * ratePartitionFiniteRatio R a d m := by
  unfold sharpRatePartitionFiniteRatio ratePartitionFiniteRatio
  ring

/-- The 300-based finite loss transfers exactly to the sharpened ratio. -/
theorem sharpRatePartition_mathematical_ratio_gt {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (hd : 519 ≤ d) :
    sharpRatePartitionGamma R a d * Real.exp (-(1677 / 1000000 : ℝ)) <
      sharpRatePartitionFiniteRatio R a d (ratePartitionMathematicalMultiplicity d) := by
  rw [sharpRatePartitionGamma_eq_scale, sharpRatePartitionFiniteRatio_eq_scale]
  simpa only [mul_assoc] using
    (mul_lt_mul_of_pos_left (ratePartition_mathematical_ratio_gt hR hRa hd)
      (by norm_num : (0 : ℝ) < 91 / 90))

end ReedSolomon.HiddenDerivative
