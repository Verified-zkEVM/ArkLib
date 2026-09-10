/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.MomentSource
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.RankBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FiniteRatio

/-!
# Finite partition source-to-rank surplus

The exact finite ratio combines the whole-simplex source moment with the local
rank envelope. The normalization keeps both the triangular enlargement and the
contact ceiling correction.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory SimplexIntegration RatePartition

/-- Exact real form of the triangular enlargement. -/
theorem partition_choose_two_real (d : ℕ) :
    ((d + 1).choose 2 : ℝ) = (d : ℝ) * (d + 1) / 2 := by
  have hnat := Nat.choose_two_right (d + 1)
  have hmul : 2 * (d + 1).choose 2 = d * (d + 1) := by
    have hdiv : 2 ∣ d * (d + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self d)
    rw [hnat, Nat.add_sub_cancel, Nat.mul_comm (d + 1) d]
    exact Nat.mul_div_cancel' hdiv
  have hreal : (2 : ℝ) * ((d + 1).choose 2 : ℝ) = (d : ℝ) * (d + 1) := by
    exact_mod_cast hmul
  linarith

/-- Multiplying the finite ratio by the rank envelope cancels to the source envelope. -/
theorem finiteGamma_mul_rankEnvelope {rate agreement : ℝ} {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m)
    (hbudget : 0 < partitionWeightBudget rate agreement d m) :
    let budget := partitionWeightBudget rate agreement d m
    finiteGamma rate agreement d m *
      (((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / budget) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / budget) ^ 2) + 1 / ((d : ℝ) / budget))) =
      (27 / 20 : ℝ) * rate * ((budget : ℝ) / d) ^ 2 *
        ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by
  dsimp only
  let budget := partitionWeightBudget rate agreement d m
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hbudgetReal : (0 : ℝ) < budget := by exact_mod_cast hbudget
  have hlambda : partitionLambda rate agreement d m = (d : ℝ) * m / budget := by
    unfold partitionLambda
    dsimp only [budget]
    simp only [div_div_eq_mul_div]
  have hexponent : -partitionLambda rate agreement d m *
      (1 + (d : ℝ) * (d + 1) / (2 * m)) =
      -((d : ℝ) / budget * (m + (d + 1).choose 2)) := by
    rw [hlambda, partition_choose_two_real]
    field_simp
  unfold finiteGamma
  dsimp only
  rw [hexponent, Real.exp_neg, hlambda]
  change _ = (27 / 20 : ℝ) * rate * ((budget : ℝ) / d) ^ 2 *
    ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2)
  have hdenom : 0 < 1 + ((d : ℝ) + 1) * ((d : ℝ) * m / budget) / m := by positivity
  field_simp
  ring

/-- The whole-simplex moment implies a strict margin for the actual finite source and rank. -/
theorem partitionSupport_finiteGamma_surplus {F : Type*} [Field F]
    {D d n m A : ℕ} {rate agreement : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hn : 0 < n) (hm : 0 < m)
    (hbudget : 0 < partitionWeightBudget rate agreement d m)
    (hrate : 0 < rate) (hagreement : 0 < agreement)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A)
    (hmoment : (27 / 10 : ℝ) < weightedSimplexExpectation d
      (partitionWeightBudget rate agreement d m)
      (fun point ↦ (max (Real.log (6 * (d : ℝ)) - (d : ℝ) * weightedRadius point /
        partitionWeightBudget rate agreement d m) 0) ^ 2)) :
    finiteGamma rate agreement d m * n *
      partitionLocalRankBound d m (partitionWeightBudget rate agreement d m) <
        (Module.finrank F (partitionSupportSpace F D d
          (partitionWeightBudget rate agreement d m) (m * A : ℕ) hD) : ℝ) := by
  have hsource := partitionSupport_dimension_gt_moment (F := F)
    hD hd hn hbudget hrate hupper hlower
    (partitionWeightBudget_level_le hrate hagreement hd) hmoment
  have hgamma : 0 < finiteGamma rate agreement d m := by
    unfold finiteGamma partitionLambda
    dsimp only
    positivity
  have hrank := mul_le_mul_of_nonneg_left
    (partitionLocalRankBound_le_geometric d m _ hd hbudget)
    (show 0 ≤ finiteGamma rate agreement d m * n by positivity)
  have hid := finiteGamma_mul_rankEnvelope (rate := rate) (agreement := agreement) hd hm hbudget
  dsimp only at hid
  have hscaled := congrArg (fun scalar : ℝ ↦ (n : ℝ) * scalar) hid
  have heq : finiteGamma rate agreement d m * n *
      (((partitionWeightBudget rate agreement d m : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / partitionWeightBudget rate agreement d m) *
          (m + (d + 1).choose 2)) *
            (1 / (((d : ℝ) + 1) * ((d : ℝ) / partitionWeightBudget rate agreement d m) ^ 2) +
              1 / ((d : ℝ) / partitionWeightBudget rate agreement d m))) =
      (27 / 20 : ℝ) * n * rate * ((partitionWeightBudget rate agreement d m : ℝ) / d) ^ 2 *
        ((partitionWeightBudget rate agreement d m : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
  rw [heq] at hrank
  exact hrank.trans_lt hsource

end ReedSolomon.HiddenDerivative
