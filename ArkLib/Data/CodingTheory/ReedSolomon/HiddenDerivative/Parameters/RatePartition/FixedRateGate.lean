/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FiniteParameters
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Recipe

/-!
# The exact fixed-rate partition gate

This file factors the limiting partition ratio without an auxiliary asymptotic slack.  The
resulting factor-six criterion supplies a sufficient derivative order at each fixed physical
rate.  It is deliberately connected to the terminating multiplicity search: the 300-based
closed multiplicity belongs to the separate uniform construction and is not asserted at this
minimal cutoff.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- The limiting ratio with its factor six exposed exactly. -/
theorem ratePartitionGamma_factorization {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hd : 0 < d) :
    ratePartitionGamma R a d =
      (9 * R / 40) * (6 * d : ℝ) ^ ((a - R) / a) * (1 + 1 / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : (0 : ℝ) < 6 * d := by positivity
  rw [ratePartitionGamma, show R / a = 1 - (a - R) / a by field_simp; ring]
  rw [Real.rpow_sub hbase, Real.rpow_one]
  field_simp [hbase.ne', hd'.ne']
  ring

/-- A factor-six order makes the main factor at least one, retaining the exact successor
factor in the limiting partition ratio. -/
theorem ratePartitionGamma_ge_one_add_inv_of_factor_six
    {R a : ℝ} {d : ℕ} (hR : 0 < R) (hRa : R < a) (hd : 0 < d)
    (horder : (1 / 6 : ℝ) * (40 / (9 * R)) ^ (a / (a - R)) ≤ d) :
    1 + 1 / (d : ℝ) ≤ ratePartitionGamma R a d := by
  have ha : 0 < a := hR.trans hRa
  have hgap : 0 < a - R := sub_pos.mpr hRa
  have hexponent : 0 < (a - R) / a := by positivity
  have hreciprocal : a / (a - R) * ((a - R) / a) = 1 := by field_simp
  have hbase : 40 / (9 * R) ≤ (6 * d : ℝ) ^ ((a - R) / a) := by
    have hscaled : (40 / (9 * R)) ^ (a / (a - R)) ≤ (6 * d : ℝ) := by
      nlinarith
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤
      (40 / (9 * R)) ^ (a / (a - R))) hscaled hexponent.le
    rw [← Real.rpow_mul (by positivity : 0 ≤ 40 / (9 * R)), hreciprocal,
      Real.rpow_one] at hp
    exact hp
  rw [ratePartitionGamma_factorization hR ha hd]
  have hfactor : (9 * R / 40) * (40 / (9 * R)) = 1 := by field_simp
  have hmain : 1 ≤ (9 * R / 40) * (6 * d : ℝ) ^ ((a - R) / a) := by
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left hbase (by positivity)
  calc
    1 + 1 / (d : ℝ) = 1 * (1 + 1 / (d : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmain (by positivity)

/-- The retained successor factor makes the factor-six limiting gate strict. -/
theorem ratePartitionGamma_gt_one_of_factor_six
    {R a : ℝ} {d : ℕ} (hR : 0 < R) (hRa : R < a) (hd : 0 < d)
    (horder : (1 / 6 : ℝ) * (40 / (9 * R)) ^ (a / (a - R)) ≤ d) :
    1 < ratePartitionGamma R a d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact (lt_add_of_pos_right 1 (one_div_pos.mpr hd')).trans_le
    (ratePartitionGamma_ge_one_add_inv_of_factor_six hR hRa hd horder)

/-- The manuscript's explicit fixed-rate ceiling, with the factor six already simplified. -/
def fixedRatePartitionOrder (R δ : ℝ) : ℕ :=
  ⌈max 500 ((20 / (27 * R)) * Real.exp (R * Real.log (40 / (9 * R)) / δ))⌉₊

/-- The explicit ceiling is in the range of the simplex moment theorem. -/
theorem fixedRatePartitionOrder_ge_500 (R δ : ℝ) :
    500 ≤ fixedRatePartitionOrder R δ := by
  exact_mod_cast (le_max_left (500 : ℝ) _ |>.trans (Nat.le_ceil _))

/-- The simplified exponential cutoff is exactly the factor-six cutoff at agreement `R+δ`. -/
theorem fixedRatePartition_cutoff_eq {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    (1 / 6 : ℝ) * (40 / (9 * R)) ^ ((R + δ) / δ) =
      (20 / (27 * R)) * Real.exp (R * Real.log (40 / (9 * R)) / δ) := by
  have hC : 0 < 40 / (9 * R) := by positivity
  rw [show (R + δ) / δ = 1 + R / δ by field_simp; ring]
  rw [Real.rpow_add hC, Real.rpow_one, Real.rpow_def_of_pos hC]
  field_simp
  ring

/-- The fixed-rate ceiling satisfies the strict limiting gate. -/
theorem fixedRatePartitionGamma_gt_one {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) :
    1 < ratePartitionGamma R (R + δ) (fixedRatePartitionOrder R δ) := by
  have hd500 := fixedRatePartitionOrder_ge_500 R δ
  have hd : 0 < fixedRatePartitionOrder R δ := by omega
  apply ratePartitionGamma_gt_one_of_factor_six hR (by linarith) hd
  rw [show R + δ - R = δ by ring]
  rw [fixedRatePartition_cutoff_eq hR hδ]
  exact (le_max_right (500 : ℝ) _).trans (Nat.le_ceil _)

/-- The older and newer presentations of the limiting ratio are definitionally equal. -/
theorem ratePartitionGamma_eq_rateGamma (R a : ℝ) (d : ℕ) :
    ratePartitionGamma R a d = RatePartition.rateGamma R a d := rfl

/-- The terminating recipe uses the same integer derivative-weight budget. -/
theorem ratePartitionWeight_eq_partitionWeightBudget (R a : ℝ) (d m : ℕ) :
    ratePartitionWeight R a d m = RatePartition.partitionWeightBudget R a d m := rfl

/-- The terminating recipe's finite ratio is exactly the rate-partition finite ratio. -/
theorem ratePartitionFiniteRatio_eq_finiteGamma (R a : ℝ) (d m : ℕ) :
    ratePartitionFiniteRatio R a d m = RatePartition.finiteGamma R a d m := by
  unfold RatePartition.finiteGamma RatePartition.partitionLambda
    RatePartition.partitionWeightBudget ratePartitionFiniteRatio ratePartitionWeight
  ring_nf

/-- The concrete multiplicity returned by the terminating least-witness search. -/
def fixedRatePartitionMultiplicity {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) : ℕ :=
  RatePartition.rateMultiplicity (rate := R) (agreement := R + δ)
    (order := fixedRatePartitionOrder R δ) hR (hR.trans (lt_add_of_pos_right R hδ))
    (lt_of_lt_of_le (by norm_num) (fixedRatePartitionOrder_ge_500 R δ))
    (by simpa only [← ratePartitionGamma_eq_rateGamma] using
      fixedRatePartitionGamma_gt_one hR hδ)

/-- The selected least multiplicity satisfies all exact finite acceptance checks. -/
theorem fixedRatePartitionMultiplicity_spec {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    let m := fixedRatePartitionMultiplicity hR hδ
    0 < m ∧ 0 < ratePartitionWeight R (R + δ) (fixedRatePartitionOrder R δ) m ∧
      1 < ratePartitionFiniteRatio R (R + δ) (fixedRatePartitionOrder R δ) m := by
  simpa only [fixedRatePartitionMultiplicity,
    ratePartitionWeight_eq_partitionWeightBudget, ratePartitionFiniteRatio_eq_finiteGamma] using
    RatePartition.rateMultiplicity_spec (rate := R) (agreement := R + δ)
      (order := fixedRatePartitionOrder R δ) hR (hR.trans (lt_add_of_pos_right R hδ))
      (lt_of_lt_of_le (by norm_num) (fixedRatePartitionOrder_ge_500 R δ))
      (by simpa only [← ratePartitionGamma_eq_rateGamma] using
        fixedRatePartitionGamma_gt_one hR hδ)

/-- Finite parameters built from the terminating least-witness multiplicity. -/
def fixedRatePartitionFiniteParameters {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    RatePartitionFiniteParameters R (R + δ) (fixedRatePartitionOrder R δ) where
  multiplicity := fixedRatePartitionMultiplicity hR hδ
  multiplicity_pos := (fixedRatePartitionMultiplicity_spec hR hδ).1
  weight_pos := (fixedRatePartitionMultiplicity_spec hR hδ).2.1
  ratio_gt_one := (fixedRatePartitionMultiplicity_spec hR hδ).2.2

/-- Thin fixed-rate margins use the terminating finite-multiplicity search.  No particular
closed multiplicity is claimed at the minimal derivative cutoff. -/
theorem exists_fixedRatePartitionFiniteParameters {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) :
    Nonempty (RatePartitionFiniteParameters R (R + δ)
      (fixedRatePartitionOrder R δ)) := by
  exact ⟨fixedRatePartitionFiniteParameters hR hδ⟩

end ReedSolomon.HiddenDerivative
