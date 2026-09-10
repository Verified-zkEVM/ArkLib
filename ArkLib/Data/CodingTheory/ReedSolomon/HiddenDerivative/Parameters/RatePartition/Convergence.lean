/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Parameters
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Choosing multiplicity from a strict rate margin

The finite ratio converges to the advertised limiting gate. Consequently every
strict margin below that gate is attained at a finite positive multiplicity.
This permits an arbitrarily small strict gate margin without imposing a fixed
rounding loss.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Filter
open scoped Topology

/-- Cancelling multiplicity expresses the finite ratio directly in its integer weight budget. -/
theorem ratePartitionFiniteRatio_eq {R a : ℝ} {d m : ℕ} (hm : 0 < m)
    (hW : 0 < ratePartitionWeight R a d m) :
    ratePartitionFiniteRatio R a d m =
      let W : ℝ := ratePartitionWeight R a d m
      (27 / 20) * R * (d + 1) *
        Real.exp (-((d : ℝ) / W * (m + (d + 1) * d / 2))) /
          (1 + (d + 1) * d / W) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hW' : (ratePartitionWeight R a d m : ℝ) ≠ 0 := by positivity
  dsimp [ratePartitionFiniteRatio]
  congr 2
  · congr 2
    field_simp
  · field_simp

/-- The integer derivative-weight budget has the required normalized limit. -/
theorem tendsto_ratePartitionWeight_div {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (fun m : ℕ ↦ (ratePartitionWeight R a d m : ℝ) / m)
      atTop (𝓝 (a * d / (R * Real.log (6 * d)))) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (6 * d) := Real.log_pos (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have hc : 0 ≤ a * d / (R * Real.log (6 * d)) := by positivity
  simpa only [Function.comp_def, ratePartitionWeight, div_eq_mul_inv,
    mul_left_comm, mul_comm, mul_assoc] using
    (tendsto_nat_floor_mul_div_atTop hc).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- All finite rounding losses vanish as multiplicity grows. -/
theorem tendsto_ratePartitionFiniteRatio {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (ratePartitionFiniteRatio R a d) atTop (𝓝 (ratePartitionGamma R a d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (6 * d) := Real.log_pos (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  let c := a * d / (R * Real.log (6 * d))
  have hc : 0 < c := by dsimp [c]; positivity
  have hw := tendsto_ratePartitionWeight_div hR ha hd
  have hlam : Tendsto (fun m : ℕ ↦ (d : ℝ) /
      ((ratePartitionWeight R a d m : ℝ) / m)) atTop (𝓝 ((d : ℝ) / c)) :=
    tendsto_const_nhds.div hw hc.ne'
  have hS := tendsto_const_div_atTop_nhds_zero_nat ((d : ℝ) * (d + 1) / 2)
  have hden := ((hlam.const_mul ((d : ℝ) + 1)).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_add 1
  have hnum := (Real.continuous_exp.tendsto _).comp
    (hlam.mul (hS.const_add 1)).neg
  have h := (hnum.const_mul ((27 / 20 : ℝ) * R * (d + 1))).div hden (by norm_num)
  simp only [add_zero, mul_one, div_one] at h
  convert h using 1
  · funext m
    simp only [ratePartitionFiniteRatio, Pi.div_apply, Function.comp_apply]
    congr 3
    ring
  · dsimp [ratePartitionGamma, c]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 6 * d)]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    field_simp

/-- A bare strict limiting gate suffices: choose multiplicity using its actual margin. -/
theorem exists_multiplicity_of_ratePartitionGamma_gt {R a γ : ℝ} {d : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hd : 0 < d)
    (hγ : γ < ratePartitionGamma R a d) :
    ∃ m : ℕ, 0 < m ∧ γ < ratePartitionFiniteRatio R a d m := by
  have he := (tendsto_ratePartitionFiniteRatio hR ha hd).eventually
    (eventually_gt_nhds hγ)
  obtain ⟨m, hm, hratio⟩ := (eventually_gt_atTop 0).and he |>.exists
  exact ⟨m, hm, hratio⟩

/-- The strict gate can be met with a positive integer derivative-weight budget as well. -/
theorem exists_positive_weight_multiplicity_of_ratePartitionGamma_gt
    {R a γ : ℝ} {d : ℕ} (hR : 0 < R) (ha : 0 < a) (hd : 0 < d)
    (hγ : γ < ratePartitionGamma R a d) :
    ∃ m : ℕ, 0 < m ∧ 0 < ratePartitionWeight R a d m ∧
      γ < ratePartitionFiniteRatio R a d m := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (6 * d) := Real.log_pos (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have hlim : 0 < a * d / (R * Real.log (6 * d)) := by positivity
  have hw := (tendsto_ratePartitionWeight_div hR ha hd).eventually
    (eventually_gt_nhds hlim)
  have hr := (tendsto_ratePartitionFiniteRatio hR ha hd).eventually
    (eventually_gt_nhds hγ)
  obtain ⟨m, hm, hw, hr⟩ := ((eventually_gt_atTop 0).and (hw.and hr)).exists
  have hW : 0 < ratePartitionWeight R a d m := by
    by_contra h
    have hz : ratePartitionWeight R a d m = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hw
  exact ⟨m, hm, hW, hr⟩

end ReedSolomon.HiddenDerivative
