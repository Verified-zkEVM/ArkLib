/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Gate
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite partition ratio and its strict-margin search

The integer derivative budget is `W=floor(m*a*d/(R*log(6*d)))`.
Writing `lambda=d/(W/m)` retains the floor error in the finite ratio
`(27/20)*R*(d+1)*exp(-lambda*(1+d*(d+1)/(2*m))) /
 (1+(d+1)*lambda/m)`.

As multiplicity increases this ratio tends to `rateGamma R a d`. Thus every strict
limiting gate permits a finite multiplicity, even when its margin is smaller than
the fixed `exp(-1/1000)` loss used by the uniform construction.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

open Filter Topology

/-- The natural derivative-order budget chosen at multiplicity `multiplicity`. -/
def partitionWeightBudget (rate agreement : ℝ) (order multiplicity : ℕ) : ℕ :=
  ⌊(multiplicity : ℝ) * agreement * order / (rate * Real.log (6 * (order : ℝ)))⌋₊

/-- Reciprocal normalized derivative radius; defined on all natural inputs. -/
def partitionLambda (rate agreement : ℝ) (order multiplicity : ℕ) : ℝ :=
  (order : ℝ) / ((partitionWeightBudget rate agreement order multiplicity : ℝ) / multiplicity)

/-- The exact finite lower ratio, before its comparison with source dimension and local rank. -/
def finiteGamma (rate agreement : ℝ) (order multiplicity : ℕ) : ℝ :=
  let lambda := partitionLambda rate agreement order multiplicity
  (27 / 20 : ℝ) * rate * (order + 1) *
    Real.exp (-lambda * (1 + (order : ℝ) * (order + 1) / (2 * multiplicity))) /
      (1 + (order + 1) * lambda / multiplicity)

/-- The limiting gate can equivalently be written with an exponential denominator. -/
theorem rateGamma_eq_exp {rate agreement : ℝ} {order : ℕ} (horder : 0 < order) :
    rateGamma rate agreement order = (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) := by
  unfold rateGamma
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 6 * order),
    Real.exp_neg, div_eq_mul_inv]
  rw [mul_comm (Real.log _) (rate / agreement)]

/-- Normalized flooring converges to the intended weighted-simplex radius. -/
theorem tendsto_partitionWeightBudget_div {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    Tendsto (fun multiplicity : ℕ ↦
      (partitionWeightBudget rate agreement order multiplicity : ℝ) / multiplicity)
      atTop (𝓝 (agreement * order / (rate * Real.log (6 * (order : ℝ))))) := by
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hraw : 0 ≤ agreement * order / (rate * Real.log (6 * (order : ℝ))) := by positivity
  have hlimit := (tendsto_nat_floor_mul_div_atTop hraw).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hlimit using 1
  funext multiplicity
  unfold partitionWeightBudget
  have heq : (multiplicity : ℝ) * agreement * order /
      (rate * Real.log (6 * (order : ℝ))) =
      (agreement * order / (rate * Real.log (6 * (order : ℝ)))) * multiplicity := by ring
  rw [heq]
  rfl

/-- The finite reciprocal radius converges with the floor error included. -/
theorem tendsto_partitionLambda {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    Tendsto (partitionLambda rate agreement order) atTop
      (𝓝 (rate / agreement * Real.log (6 * (order : ℝ)))) := by
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hraw : 0 < agreement * order / (rate * Real.log (6 * (order : ℝ))) := by positivity
  have hlimit := (tendsto_const_nhds (x := (order : ℝ))).div
    (tendsto_partitionWeightBudget_div hrate hagreement horder) hraw.ne'
  have hequal : (order : ℝ) / (agreement * order / (rate * Real.log (6 * (order : ℝ)))) =
      rate / agreement * Real.log (6 * (order : ℝ)) := by
    have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
    field_simp
  change Tendsto (fun multiplicity ↦ (order : ℝ) /
    ((partitionWeightBudget rate agreement order multiplicity : ℝ) / multiplicity)) _ _
  simpa only [hequal, Pi.div_def] using hlimit

/-- The exact finite ratios converge to the analytic gate at every positive rate and order. -/
theorem tendsto_finiteGamma {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    Tendsto (finiteGamma rate agreement order) atTop (𝓝 (rateGamma rate agreement order)) := by
  let lambda := rate / agreement * Real.log (6 * (order : ℝ))
  have hlambda := tendsto_partitionLambda hrate hagreement horder
  have htri : Tendsto (fun multiplicity : ℕ ↦
      (order : ℝ) * (order + 1) / (2 * multiplicity)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun multiplicity : ℕ ↦
        ((order : ℝ) * (order + 1) / 2) / multiplicity) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [div_div] using hdiv
  have hexponent : Tendsto (fun multiplicity : ℕ ↦
      -partitionLambda rate agreement order multiplicity *
        (1 + (order : ℝ) * (order + 1) / (2 * multiplicity))) atTop (𝓝 (-lambda)) := by
    simpa only [add_zero, mul_one] using
      hlambda.neg.mul ((tendsto_const_nhds (x := (1 : ℝ))).add htri)
  have hdenominator : Tendsto (fun multiplicity : ℕ ↦
      1 + ((order : ℝ) + 1) * partitionLambda rate agreement order multiplicity / multiplicity)
      atTop (𝓝 1) := by
    have hzero := ((tendsto_const_nhds (x := (order : ℝ) + 1)).mul hlambda).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have hexp := (Real.continuous_exp.tendsto (-lambda)).comp hexponent
  have hlimit := ((tendsto_const_nhds
    (x := (27 / 20 : ℝ) * rate * (order + 1))).mul hexp).div hdenominator one_ne_zero
  rw [rateGamma_eq_exp horder]
  change Tendsto (fun multiplicity ↦ (27 / 20 : ℝ) * rate * (order + 1) *
    Real.exp (-partitionLambda rate agreement order multiplicity *
      (1 + (order : ℝ) * (order + 1) / (2 * multiplicity))) /
        (1 + (order + 1) * partitionLambda rate agreement order multiplicity / multiplicity)) _ _
  simpa only [div_one, lambda, Pi.div_def, Function.comp_apply] using hlimit

/-- Flooring the derivative radius only lowers the source integral's reference level. -/
theorem partitionWeightBudget_level_le {rate agreement : ℝ} {order multiplicity : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order) :
    rate * partitionWeightBudget rate agreement order multiplicity / order *
      Real.log (6 * (order : ℝ)) ≤ multiplicity * agreement := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hfloor := Nat.floor_le (show 0 ≤ (multiplicity : ℝ) * agreement * order /
    (rate * Real.log (6 * (order : ℝ))) by positivity)
  have hbound := mul_le_mul_of_nonneg_left hfloor
    (show 0 ≤ rate / order * Real.log (6 * (order : ℝ)) by positivity)
  change rate * (⌊(multiplicity : ℝ) * agreement * order /
    (rate * Real.log (6 * (order : ℝ)))⌋₊ : ℝ) / order * _ ≤ _
  have heq : rate / (order : ℝ) * Real.log (6 * (order : ℝ)) *
      ((multiplicity : ℝ) * agreement * order / (rate * Real.log (6 * (order : ℝ)))) =
      multiplicity * agreement := by
    have hlog' : Real.log ((order : ℝ) * 6) ≠ 0 := by simpa [mul_comm] using hlog.ne'
    field_simp [hrate.ne', horderReal.ne', hlog.ne', hlog']
  rw [heq] at hbound
  calc
    _ = rate / (order : ℝ) * Real.log (6 * (order : ℝ)) *
      (⌊(multiplicity : ℝ) * agreement * order /
        (rate * Real.log (6 * (order : ℝ)))⌋₊ : ℝ) := by ring
    _ ≤ _ := hbound

/-- Every strict limiting margin admits a finite positive multiplicity and derivative budget. -/
theorem exists_finiteGamma_gt_one {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hagreement : 0 < agreement) (horder : 0 < order)
    (hgate : 1 < rateGamma rate agreement order) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < finiteGamma rate agreement order multiplicity := by
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast horder
    linarith)
  have hraw : 0 < agreement * order / (rate * Real.log (6 * (order : ℝ))) := by positivity
  have hbudget : Tendsto (partitionWeightBudget rate agreement order) atTop atTop := by
    have hlim := tendsto_nat_floor_mul_atTop
      (agreement * order / (rate * Real.log (6 * (order : ℝ)))) hraw
    convert hlim using 1
    funext multiplicity
    unfold partitionWeightBudget
    congr 1
    ring
  have hpositive := hbudget.eventually (eventually_gt_atTop 0)
  have hratio := (tendsto_finiteGamma hrate hagreement horder).eventually
    (isOpen_Ioi.mem_nhds hgate)
  obtain ⟨multiplicity, hm, hW, hfinite⟩ :=
    ((eventually_gt_atTop 0).and (hpositive.and hratio)).exists
  exact ⟨multiplicity, hm, hW, hfinite⟩

end ReedSolomon.HiddenDerivative.RatePartition
