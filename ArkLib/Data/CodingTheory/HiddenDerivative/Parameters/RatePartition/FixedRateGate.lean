/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Recipe

/-!
# Finite parameters at the fixed-rate partition gate

The fixed-rate order satisfies the strict limiting gate at agreement `R + δ`. The least
multiplicity selected by `rateMultiplicity` then gives positive finite weight and a finite ratio
strictly greater than one.

## Main statements

* `fixedRatePartitionMultiplicity`, `fixedRatePartitionMultiplicity_spec`: the least accepted
  multiplicity and its finite checks.
* `fixedRatePartitionFiniteParameters`: the selected finite parameters at the fixed-rate order.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The least multiplicity with positive weight budget and finite ratio above one at the
fixed-rate order and agreement `R + δ`. -/
noncomputable def fixedRatePartitionMultiplicity {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) : ℕ :=
  rateMultiplicity hrate (by linarith) (by
    have horder := fixedRatePartitionOrder_ge_500 rate gap
    omega) (fixedRateGamma_gt_one hrate hgap)

/-- The selected fixed-rate multiplicity has positive weight budget and finite ratio above one. -/
theorem fixedRatePartitionMultiplicity_spec {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) :
    let multiplicity := fixedRatePartitionMultiplicity hrate hgap
    0 < multiplicity ∧
      0 < partitionWeightBudget rate (rate + gap) (fixedRatePartitionOrder rate gap)
        multiplicity ∧
      1 < partitionFiniteRatio rate (rate + gap) (fixedRatePartitionOrder rate gap)
        multiplicity := by
  have hagreement : 0 < rate + gap := by linarith
  have horder : 0 < fixedRatePartitionOrder rate gap := by
    have hbound := fixedRatePartitionOrder_ge_500 rate gap
    omega
  simpa only [fixedRatePartitionMultiplicity] using
    (rateMultiplicity_spec hrate hagreement horder (fixedRateGamma_gt_one hrate hgap))

/-- Finite parameters built from the least fixed-rate multiplicity. -/
noncomputable def fixedRatePartitionFiniteParameters {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) :
    PartitionFiniteParameters rate (rate + gap) (fixedRatePartitionOrder rate gap) where
  multiplicity := fixedRatePartitionMultiplicity hrate hgap
  multiplicity_pos := (fixedRatePartitionMultiplicity_spec hrate hgap).1
  weightBudget_pos := (fixedRatePartitionMultiplicity_spec hrate hgap).2.1
  one_lt_finiteRatio := (fixedRatePartitionMultiplicity_spec hrate hgap).2.2

end ReedSolomon.HiddenDerivative.RatePartition
