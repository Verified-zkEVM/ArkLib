/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Ratio
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Moment

/-! # The unconditional finite source/rank inequality for the rate-partition support -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- Every selected finite parameter choice gives the actual source/rank surplus. -/
theorem ratePartition_dimension_gt_finiteRatio
    {D d m n A : ℕ} {R a : ℝ}
    (hD : 0 < D) (hd : 500 ≤ d) (hm : 0 < m) (hn : 0 < n)
    (hR : 0 < R) (ha : 0 < a) (hW : 0 < ratePartitionWeight R a d m)
    (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A) :
    ratePartitionFiniteRatio R a d m * n *
      ratePartitionRankBound d m (ratePartitionWeight R a d m) <
      ((ratePartitionExponents D d (ratePartitionWeight R a d m)
        (m * A : ℕ) hD).card : ℝ) := by
  apply ratePartition_dimension_gt_ratio_of_moment hD (by omega) hm hn hR ha hW hDn haA
  exact RatePartition.weightedSimplexMoment_gt hd (by exact_mod_cast hW)

end ReedSolomon.HiddenDerivative
