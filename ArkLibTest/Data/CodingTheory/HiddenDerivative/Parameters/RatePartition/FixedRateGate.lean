/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FixedRateGate

/-!
# Fixed-rate partition gate acceptance tests

Concrete strict-gate and finite-multiplicity cases, including the zero-gap boundary.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- At rate `1/2` and gap `1/4`, the selected derivative order gives a strict gate. -/
example : 1 < rateGamma (1 / 2) (1 / 2 + 1 / 4)
    (fixedRatePartitionOrder (1 / 2) (1 / 4)) := by
  exact fixedRateGamma_gt_one (by norm_num) (by norm_num)

/-- At rate `1/2` and gap `1/4`, the selected multiplicity passes the finite checks. -/
example :
    let multiplicity := fixedRatePartitionMultiplicity (rate := 1 / 2) (gap := 1 / 4)
      (by norm_num) (by norm_num)
    0 < multiplicity ∧
      0 < partitionWeightBudget (1 / 2) (1 / 2 + 1 / 4)
        (fixedRatePartitionOrder (1 / 2) (1 / 4)) multiplicity ∧
      1 < partitionFiniteRatio (1 / 2) (1 / 2 + 1 / 4)
        (fixedRatePartitionOrder (1 / 2) (1 / 4)) multiplicity :=
  fixedRatePartitionMultiplicity_spec (rate := 1 / 2) (gap := 1 / 4)
    (by norm_num) (by norm_num)

/-- Finite parameters exist at rate `1/2` and gap `1/4`. -/
example : Nonempty (PartitionFiniteParameters (1 / 2) (1 / 2 + 1 / 4)
    (fixedRatePartitionOrder (1 / 2) (1 / 4))) := by
  exact exists_fixedRatePartitionFiniteParameters (by norm_num) (by norm_num)

/-- At zero gap, order `500` does not pass the limiting gate at rate `1/2`. -/
example : ¬ 1 < rateGamma (1 / 2) (1 / 2) 500 := by
  norm_num [rateGamma]

end ReedSolomon.HiddenDerivative.RatePartition
