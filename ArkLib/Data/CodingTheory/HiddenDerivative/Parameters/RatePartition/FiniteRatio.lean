/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The finite partition ratio and its limit

At code rate `R`, agreement fraction `a`, derivative order `d` and multiplicity `m`, the
rate-dependent partition construction uses the natural derivative-weight budget
`W = ⌊m a d / (R log(6d))⌋₊`. With the inverse radius `λ = d / (W/m) = d m / W`, the finite
ratio is

```text
(27/20) R (d + 1) exp(-λ (1 + d (d + 1) / (2m))) / (1 + (d + 1) λ / m),
```

which keeps every rounding term. As `m → ∞`, `W/m → a d / (R log(6d))`, so
`λ → (R/a) log(6d)`, and the finite ratio tends to `(27/20) R (d + 1) exp(-(R/a) log(6d))`,
which is `(27/20) R (d + 1) / (6d)^(R/a)`. Consequently every value below that limit is exceeded
at some finite positive multiplicity with a positive weight budget; no fixed rounding loss has to
be assumed.

## Main definitions

* `partitionWeightBudget`, `partitionInverseRadius`, `partitionFiniteRatio`: `W`, `λ` and the
  finite ratio above.
* `PartitionFiniteParameters`: a positive multiplicity with positive weight budget whose finite
  ratio exceeds `1`.

## Main statements

* `partitionInverseRadius_eq`: `λ = d m / W`.
* `partitionFiniteRatio_eq_weightBudget`: the finite ratio written with `W` in place of `λ`.
* `tendsto_partitionWeightBudget_div`, `tendsto_partitionInverseRadius`,
  `tendsto_partitionFiniteRatio`: the three limits above.
* `exists_partitionFiniteRatio_gt`: every value below the limit is exceeded at some positive
  multiplicity with positive weight budget.
* `leastPartitionFiniteMultiplicity` and its specification: the first multiplicity whose finite
  ratio exceeds `1` and whose weight budget is positive.
* `PartitionFiniteParameters.nonempty`: such parameters exist when the limit exceeds `1`.
* The fixed-rate multiplicity and finite-parameter results specialize these APIs at `R + δ`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

open Filter Topology

/-- The derivative-weight budget `W = ⌊m a d / (R log(6d))⌋₊` at code rate `R`, agreement
fraction `a`, derivative order `d` and multiplicity `m`. -/
def partitionWeightBudget (rate agreement : ℝ) (order multiplicity : ℕ) : ℕ :=
  ⌊(multiplicity : ℝ) * agreement * order / (rate * Real.log (6 * (order : ℝ)))⌋₊

/-- The inverse normalized derivative radius `λ = d / (W/m)`, where `W` is the weight budget
`partitionWeightBudget`. It equals `d m / W`; see `partitionInverseRadius_eq`. -/
def partitionInverseRadius (rate agreement : ℝ) (order multiplicity : ℕ) : ℝ :=
  (order : ℝ) / ((partitionWeightBudget rate agreement order multiplicity : ℝ) / multiplicity)

/-- The finite partition ratio
`(27/20) R (d + 1) exp(-λ (1 + d (d + 1) / (2m))) / (1 + (d + 1) λ / m)`, where `λ` is
`partitionInverseRadius`. -/
def partitionFiniteRatio (rate agreement : ℝ) (order multiplicity : ℕ) : ℝ :=
  let lambda := partitionInverseRadius rate agreement order multiplicity
  (27 / 20 : ℝ) * rate * (order + 1) *
    Real.exp (-lambda * (1 + (order : ℝ) * (order + 1) / (2 * multiplicity))) /
      (1 + (order + 1) * lambda / multiplicity)

/-- The inverse radius is `d m / W`. -/
theorem partitionInverseRadius_eq (rate agreement : ℝ) (order multiplicity : ℕ) :
    partitionInverseRadius rate agreement order multiplicity =
      (order : ℝ) * multiplicity / partitionWeightBudget rate agreement order multiplicity :=
  div_div_eq_mul_div _ _ _

/-- The inverse radius is nonnegative. -/
theorem partitionInverseRadius_nonneg (rate agreement : ℝ) (order multiplicity : ℕ) :
    0 ≤ partitionInverseRadius rate agreement order multiplicity := by
  rw [partitionInverseRadius_eq]
  positivity

/-- For positive `m` and `W`, the finite ratio is
`(27/20) R (d + 1) exp(-(d/W) (m + (d + 1) d / 2)) / (1 + (d + 1) d / W)`. -/
theorem partitionFiniteRatio_eq_weightBudget {rate agreement : ℝ} {order multiplicity : ℕ}
    (hmultiplicity : 0 < multiplicity)
    (hbudget : 0 < partitionWeightBudget rate agreement order multiplicity) :
    partitionFiniteRatio rate agreement order multiplicity =
      let budget : ℝ := partitionWeightBudget rate agreement order multiplicity
      (27 / 20) * rate * (order + 1) *
        Real.exp (-((order : ℝ) / budget * (multiplicity + (order + 1) * order / 2))) /
          (1 + (order + 1) * order / budget) := by
  have hm : (multiplicity : ℝ) ≠ 0 := by positivity
  have hW : (partitionWeightBudget rate agreement order multiplicity : ℝ) ≠ 0 := by positivity
  simp only [partitionFiniteRatio, partitionInverseRadius_eq]
  congr 2
  · congr 1
    field_simp
  · field_simp

/-- The normalized weight budget `W/m` tends to `a d / (R log(6d))` as `m → ∞`. -/
theorem tendsto_partitionWeightBudget_div {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    Tendsto (fun multiplicity : ℕ ↦
      (partitionWeightBudget rate agreement order multiplicity : ℝ) / multiplicity)
      atTop (𝓝 (agreement * order / (rate * Real.log (6 * (order : ℝ))))) := by
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hlimit := (tendsto_nat_floor_mul_div_atTop
    (show 0 ≤ agreement * order / (rate * Real.log (6 * (order : ℝ))) by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hlimit using 1
  funext multiplicity
  simp only [Function.comp_apply, partitionWeightBudget]
  congr 3
  ring

/-- The inverse radius `λ` tends to `(R/a) log(6d)` as `m → ∞`. -/
theorem tendsto_partitionInverseRadius {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    Tendsto (partitionInverseRadius rate agreement order) atTop
      (𝓝 (rate / agreement * Real.log (6 * (order : ℝ)))) := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hlimit := (tendsto_const_nhds (x := (order : ℝ))).div
    (tendsto_partitionWeightBudget_div hrate hagreement horder)
    (show agreement * order / (rate * Real.log (6 * (order : ℝ))) ≠ 0 by positivity)
  have hequal : (order : ℝ) / (agreement * order / (rate * Real.log (6 * (order : ℝ)))) =
      rate / agreement * Real.log (6 * (order : ℝ)) := by
    field_simp
  rw [hequal] at hlimit
  exact hlimit

/-- The finite ratio tends to `(27/20) R (d + 1) exp(-(R/a) log(6d))` as `m → ∞`. -/
theorem tendsto_partitionFiniteRatio {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    Tendsto (partitionFiniteRatio rate agreement order) atTop
      (𝓝 ((27 / 20 : ℝ) * rate * (order + 1) *
        Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))))) := by
  have hlambda := tendsto_partitionInverseRadius hrate hagreement horder
  have htriangle : Tendsto (fun multiplicity : ℕ ↦
      (order : ℝ) * (order + 1) / (2 * multiplicity)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun multiplicity : ℕ ↦
        ((order : ℝ) * (order + 1) / 2) / multiplicity) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [div_div] using hdiv
  have hexponent := hlambda.neg.mul ((tendsto_const_nhds (x := (1 : ℝ))).add htriangle)
  have hdenominator := (tendsto_const_nhds (x := (1 : ℝ))).add
    (((tendsto_const_nhds (x := (order : ℝ) + 1)).mul hlambda).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlimit := ((tendsto_const_nhds (x := (27 / 20 : ℝ) * rate * (order + 1))).mul
    ((Real.continuous_exp.tendsto _).comp hexponent)).div hdenominator (by norm_num)
  simp only [add_zero, mul_one, div_one] at hlimit
  exact hlimit

/-- Every value `γ` below the limit `(27/20) R (d + 1) exp(-(R/a) log(6d))` is exceeded by the
finite ratio at some positive multiplicity with positive weight budget. -/
theorem exists_partitionFiniteRatio_gt {rate agreement γ : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hγ : γ < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ))))) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget rate agreement order multiplicity ∧
      γ < partitionFiniteRatio rate agreement order multiplicity := by
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hbudget := (tendsto_partitionWeightBudget_div hrate hagreement horder).eventually
    (eventually_gt_nhds
      (show 0 < agreement * order / (rate * Real.log (6 * (order : ℝ))) by positivity))
  have hratio := (tendsto_partitionFiniteRatio hrate hagreement horder).eventually
    (eventually_gt_nhds hγ)
  obtain ⟨multiplicity, hm, hW, hfinite⟩ :=
    ((eventually_gt_atTop 0).and (hbudget.and hratio)).exists
  refine ⟨multiplicity, hm, ?_, hfinite⟩
  by_contra hzero
  rw [Nat.eq_zero_of_not_pos hzero, Nat.cast_zero, zero_div] at hW
  exact lt_irrefl _ hW

/-- The least multiplicity whose weight budget is positive and finite ratio exceeds `1`. -/
noncomputable def leastPartitionFiniteMultiplicity {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hlimit : 1 < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ))))) : ℕ := by
  classical
  exact Nat.find (exists_partitionFiniteRatio_gt hrate hagreement horder hlimit)

/-- The least multiplicity passes all finite acceptance checks. -/
theorem leastPartitionFiniteMultiplicity_spec {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hlimit : 1 < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ))))) :
    let multiplicity := leastPartitionFiniteMultiplicity hrate hagreement horder hlimit
    0 < multiplicity ∧ 0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  classical
  exact Nat.find_spec (exists_partitionFiniteRatio_gt hrate hagreement horder hlimit)

/-- The least multiplicity is no greater than any candidate passing the finite checks. -/
theorem leastPartitionFiniteMultiplicity_minimal {rate agreement : ℝ} {order candidate : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hlimit : 1 < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))))
    (hcandidate : 0 < candidate ∧
      0 < partitionWeightBudget rate agreement order candidate ∧
      1 < partitionFiniteRatio rate agreement order candidate) :
    leastPartitionFiniteMultiplicity hrate hagreement horder hlimit ≤ candidate := by
  classical
  exact Nat.find_min' (exists_partitionFiniteRatio_gt hrate hagreement horder hlimit) hcandidate

/-- The least multiplicity for the fixed-rate order and agreement `R + δ`. -/
noncomputable def fixedRatePartitionMultiplicity {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) : ℕ := by
  have hagreement : 0 < rate + gap := by linarith
  have horder500 := fixedRatePartitionOrder_ge_500 rate gap
  have horder : 0 < fixedRatePartitionOrder rate gap := by
    omega
  refine leastPartitionFiniteMultiplicity hrate hagreement horder ?_
  rw [← rateGamma_eq_exponential horder]
  exact fixedRateGamma_gt_one hrate hgap

/-- The least fixed-rate multiplicity has a positive weight budget and finite ratio above `1`. -/
theorem fixedRatePartitionMultiplicity_spec {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) :
    let multiplicity := fixedRatePartitionMultiplicity hrate hgap
    0 < multiplicity ∧
      0 < partitionWeightBudget rate (rate + gap) (fixedRatePartitionOrder rate gap)
        multiplicity ∧
    1 < partitionFiniteRatio rate (rate + gap) (fixedRatePartitionOrder rate gap)
        multiplicity := by
  have hagreement : 0 < rate + gap := by linarith
  have horder500 := fixedRatePartitionOrder_ge_500 rate gap
  have horder : 0 < fixedRatePartitionOrder rate gap := by omega
  unfold fixedRatePartitionMultiplicity
  exact leastPartitionFiniteMultiplicity_spec hrate hagreement horder (by
    rw [← rateGamma_eq_exponential horder]
    exact fixedRateGamma_gt_one hrate hgap)

/-- A positive multiplicity with positive weight budget at which the finite ratio exceeds `1`,
at code rate `R`, agreement fraction `a` and derivative order `d`. -/
structure PartitionFiniteParameters (rate agreement : ℝ) (order : ℕ) where
  /-- The multiplicity `m`. -/
  multiplicity : ℕ
  /-- The multiplicity is positive. -/
  multiplicity_pos : 0 < multiplicity
  /-- The weight budget at this multiplicity is positive. -/
  weightBudget_pos : 0 < partitionWeightBudget rate agreement order multiplicity
  /-- The finite ratio at this multiplicity exceeds `1`. -/
  one_lt_finiteRatio : 1 < partitionFiniteRatio rate agreement order multiplicity

/-- Finite parameters at the fixed-rate order and agreement `R + δ`. -/
noncomputable def fixedRatePartitionFiniteParameters {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) :
    PartitionFiniteParameters rate (rate + gap) (fixedRatePartitionOrder rate gap) where
  multiplicity := fixedRatePartitionMultiplicity hrate hgap
  multiplicity_pos := (fixedRatePartitionMultiplicity_spec hrate hgap).1
  weightBudget_pos := (fixedRatePartitionMultiplicity_spec hrate hgap).2.1
  one_lt_finiteRatio := (fixedRatePartitionMultiplicity_spec hrate hgap).2.2

/-- Fixed-rate parameters exist at the order `fixedRatePartitionOrder R δ`. -/
theorem exists_fixedRatePartitionFiniteParameters {rate gap : ℝ}
    (hrate : 0 < rate) (hgap : 0 < gap) :
    Nonempty (PartitionFiniteParameters rate (rate + gap)
      (fixedRatePartitionOrder rate gap)) := by
  exact ⟨fixedRatePartitionFiniteParameters hrate hgap⟩

/-- Finite parameters exist whenever the limit `(27/20) R (d + 1) exp(-(R/a) log(6d))` of the
finite ratio exceeds `1`. -/
theorem PartitionFiniteParameters.nonempty {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hlimit : 1 < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ))))) :
    Nonempty (PartitionFiniteParameters rate agreement order) := by
  obtain ⟨m, hm, hW, hratio⟩ := exists_partitionFiniteRatio_gt hrate hagreement horder hlimit
  exact ⟨⟨m, hm, hW, hratio⟩⟩

end ReedSolomon.HiddenDerivative.RatePartition
