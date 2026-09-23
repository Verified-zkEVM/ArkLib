/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate

/-!
# The least multiplicity passing the finite partition gate

When the limiting rate ratio is strictly above one, some positive multiplicity has a positive
weight budget and finite ratio above one. This module chooses the least such multiplicity and
records its acceptance conditions.

## Main statements

* `rateMultiplicity`: the least multiplicity with positive budget and finite ratio above one.
* `rateMultiplicity_spec`, `rateMultiplicity_minimal`: acceptance and minimality properties.
* `exists_partitionFiniteParameters_of_rateGamma_gt_one`: a strict limiting gate gives a finite
  multiplicity passing the finite gate.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem rateGamma_eq_exponential_limit {rate agreement : ℝ} {order : ℕ}
    (horder : 0 < order) :
    rateGamma rate agreement order =
      (27 / 20 : ℝ) * rate * (order + 1) *
        Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) := by
  have hbase : 0 < (6 * (order : ℝ)) := by positivity
  unfold rateGamma
  rw [Real.rpow_def_of_pos hbase, div_eq_mul_inv, Real.exp_neg]
  apply congrArg (fun x : ℝ => (27 / 20 : ℝ) * rate * (order + 1) * x)
  apply congrArg (fun x : ℝ => x⁻¹)
  apply congrArg Real.exp
  ring

/-- A strict limiting gate gives a positive multiplicity with positive weight budget and finite
ratio above one. -/
theorem exists_partitionFiniteParameters_of_rateGamma_gt_one {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  have hlimit :
      1 < (27 / 20 : ℝ) * rate * (order + 1) *
        Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) := by
    rw [← rateGamma_eq_exponential_limit horder]
    exact hgate
  exact exists_partitionFiniteRatio_gt hrate hagreement horder hlimit

/-- The first multiplicity with positive weight budget and finite ratio above one. -/
def rateMultiplicity {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) : ℕ := by
  classical
  exact Nat.find
    (exists_partitionFiniteParameters_of_rateGamma_gt_one hrate hagreement horder hgate)

/-- The selected multiplicity has positive weight budget and finite ratio above one. -/
theorem rateMultiplicity_spec {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) :
    let multiplicity := rateMultiplicity hrate hagreement horder hgate
    0 < multiplicity ∧ 0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  classical
  simpa only [rateMultiplicity] using
    Nat.find_spec
      (exists_partitionFiniteParameters_of_rateGamma_gt_one hrate hagreement horder hgate)

/-- No smaller multiplicity has positive weight budget and finite ratio above one. -/
theorem rateMultiplicity_minimal {rate agreement : ℝ} {order candidate : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order)
    (hcandidate : 0 < candidate ∧
      0 < partitionWeightBudget rate agreement order candidate ∧
      1 < partitionFiniteRatio rate agreement order candidate) :
    rateMultiplicity hrate hagreement horder hgate ≤ candidate := by
  classical
  simpa only [rateMultiplicity] using Nat.find_min'
    (exists_partitionFiniteParameters_of_rateGamma_gt_one hrate hagreement horder hgate)
    hcandidate

end ReedSolomon.HiddenDerivative.RatePartition
