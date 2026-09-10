/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.RoundingLoss

/-! # Finite ratio at the closed multiplicity -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- The closed multiplicity loses strictly less than one thousandth logarithmically. -/
theorem ratePartition_closed_ratio_gt {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (hd : 500 ≤ d) :
    ratePartitionGamma R a d * Real.exp (-(1 / 1000 : ℝ)) <
      ratePartitionFiniteRatio R a d (ratePartitionClosedMultiplicity d) := by
  obtain ⟨hm, hW, hlam, herror⟩ := ratePartition_closed_floor_bounds hR hRa hd
  let m := ratePartitionClosedMultiplicity d
  let W := ratePartitionWeight R a d m
  let L := Real.log (6 * d)
  let lam := (d : ℝ) * m / W
  let lam0 := R * L / a
  have hd' : (500 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hLupper : L ≤ 6 * d := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 * d)
    dsimp [L]
    linarith
  have hden : 0 < 1 + ((d : ℝ) + 1) * lam / m := by dsimp [lam]; positivity
  let loss := lam - lam0 + lam * ((d : ℝ) * (d + 1) / 2) / m +
    Real.log (1 + ((d : ℝ) + 1) * lam / m)
  have hloss : loss < 1 / 1000 := ratePartition_rounding_loss_lt hd' hL hLupper
    (Nat.le_ceil _) (by dsimp [lam]; positivity) hlam herror
  have hGamma : ratePartitionGamma R a d = (27 / 20) * R * (d + 1) *
      Real.exp (-lam0) := by
    dsimp [ratePartitionGamma, lam0, L]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 6 * d)]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  have heq : ratePartitionFiniteRatio R a d m =
      ratePartitionGamma R a d * Real.exp (-loss) := by
    rw [hGamma, mul_assoc, ← Real.exp_add]
    dsimp [ratePartitionFiniteRatio]
    have hlameq : (d : ℝ) / ((W : ℝ) / m) = lam := by dsimp [lam]; field_simp
    change (27 / 20) * R * (d + 1) *
      Real.exp (-((d : ℝ) / ((W : ℝ) / m)) * (1 + (d * (d + 1) / 2) / m)) /
      (1 + (d + 1) * ((d : ℝ) / ((W : ℝ) / m)) / m) = _
    rw [hlameq, div_eq_mul_inv]
    have hinv : (1 + ((d : ℝ) + 1) * lam / m)⁻¹ =
        Real.exp (-Real.log (1 + ((d : ℝ) + 1) * lam / m)) := by
      rw [Real.exp_neg, Real.exp_log hden]
    rw [hinv]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [loss]
    ring
  rw [heq]
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (neg_lt_neg hloss))
  rw [hGamma]
  positivity

end ReedSolomon.HiddenDerivative
