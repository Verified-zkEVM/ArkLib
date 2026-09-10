/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Convergence

/-! # A finite parameter choice from any strict partition gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- A multiplicity chosen before the code, retaining its actual strict finite ratio. -/
structure RatePartitionFiniteParameters (R a : ℝ) (d : ℕ) where
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  weight_pos : 0 < ratePartitionWeight R a d multiplicity
  ratio_gt_one : 1 < ratePartitionFiniteRatio R a d multiplicity

/-- Every bare strict limiting gate supplies finite parameters; no fixed loss is assumed. -/
theorem exists_ratePartitionFiniteParameters {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hd : 0 < d)
    (hgate : 1 < ratePartitionGamma R a d) :
    Nonempty (RatePartitionFiniteParameters R a d) := by
  obtain ⟨m, hm, hW, hr⟩ := exists_positive_weight_multiplicity_of_ratePartitionGamma_gt
    hR ha hd hgate
  exact ⟨⟨m, hm, hW, hr⟩⟩

end ReedSolomon.HiddenDerivative
