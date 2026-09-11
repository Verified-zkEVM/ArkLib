/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateBound
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The stationary root on the low-rate first-order branch

For positive rate `rho`, the low-rate optimizer is encoded by the unique positive solution

`u² (u + 3) = sqrt (rho / 2)`.

The branch condition is stated in its intrinsic form
`sqrt(rho/2) * (sqrt(rho/2) + 3) < 1`.  At equality this is the manuscript cutoff
`rho = 11 - 3 sqrt 13`; keeping the intrinsic condition avoids making the analytic optimizer
depend on a particular closed-form presentation of that cutoff.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- Cubic whose positive inverse defines the low-rate stationary parameter. -/
def firstOrderStationaryCubic (u : ℝ) : ℝ := u ^ 2 * (u + 3)

/-- The scale `sqrt(rho/2)` appearing in the stationary equations. -/
def firstOrderLowRateScale (rho : ℝ) : ℝ := Real.sqrt (rho / 2)

/-- The rate at which the stationary optimizer reaches derivative ratio `1/2`. -/
def firstOrderRateSwitch : ℝ := 11 - 3 * Real.sqrt 13

/-- Intrinsic open low-rate branch condition. -/
def FirstOrderLowRateRegime (rho : ℝ) : Prop :=
  firstOrderLowRateScale rho * (firstOrderLowRateScale rho + 3) < 1

theorem firstOrderLowRateScale_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < firstOrderLowRateScale rho := by
  unfold firstOrderLowRateScale
  exact Real.sqrt_pos.2 (by positivity)

theorem firstOrderLowRateScale_sq {rho : ℝ} (hrho : 0 ≤ rho) :
    firstOrderLowRateScale rho ^ 2 = rho / 2 := by
  unfold firstOrderLowRateScale
  exact Real.sq_sqrt (by positivity)

/-- The intrinsic stationary-branch condition is exactly the manuscript cutoff. -/
theorem firstOrderLowRateRegime_iff_lt_rateSwitch {rho : ℝ} (hrho : 0 ≤ rho) :
    FirstOrderLowRateRegime rho ↔ rho < firstOrderRateSwitch := by
  let r := Real.sqrt 13
  let t := firstOrderLowRateScale rho
  let b := (r - 3) / 2
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = 13 := by
    dsimp only [r]
    exact Real.sq_sqrt (by norm_num)
  have hr3 : 3 < r := by nlinarith
  have hb0 : 0 ≤ b := by dsimp only [b]; linarith
  have ht0 : 0 ≤ t := by dsimp only [t, firstOrderLowRateScale]; positivity
  have htSq : t ^ 2 = rho / 2 := by
    dsimp only [t]
    exact firstOrderLowRateScale_sq hrho
  have hbSq : b ^ 2 = firstOrderRateSwitch / 2 := by
    dsimp only [b, firstOrderRateSwitch]
    nlinarith
  have hbBoundary : b * (b + 3) = 1 := by
    dsimp only [b]
    nlinarith
  have hbranch : t * (t + 3) < 1 ↔ t < b := by
    constructor
    · intro h
      by_contra hnot
      have hbt : b ≤ t := le_of_not_gt hnot
      have hnonneg : 0 ≤ (t - b) * (t + b + 3) := by positivity
      nlinarith
    · intro htb
      have hnonneg : 0 < (b - t) * (b + t + 3) := by positivity
      nlinarith
  change t * (t + 3) < 1 ↔ rho < firstOrderRateSwitch
  rw [hbranch]
  rw [← sq_lt_sq₀ ht0 hb0, htSq, hbSq]
  constructor <;> intro h <;> linarith

theorem firstOrderStationaryCubic_strictMonoOn :
    StrictMonoOn firstOrderStationaryCubic (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hyPos : 0 < y := hx0.trans_lt hxy
  have hfactor : 0 < y ^ 2 + x * y + x ^ 2 + 3 * (x + y) := by
    have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hdiff :
      firstOrderStationaryCubic y - firstOrderStationaryCubic x =
        (y - x) * (y ^ 2 + x * y + x ^ 2 + 3 * (x + y)) := by
    unfold firstOrderStationaryCubic
    ring
  rw [← sub_pos, hdiff]
  exact mul_pos (sub_pos.mpr hxy) hfactor

theorem exists_firstOrderStationaryRoot {rho : ℝ} (hrho : 0 < rho) :
    ∃ u : ℝ, 0 < u ∧
      firstOrderStationaryCubic u = firstOrderLowRateScale rho := by
  let t := firstOrderLowRateScale rho
  have ht : 0 < t := firstOrderLowRateScale_pos hrho
  have hupper : t ≤ firstOrderStationaryCubic (t + 1) := by
    have hone : 1 ≤ (t + 1) ^ 2 := by nlinarith [sq_nonneg t]
    have hright : 0 ≤ t + 4 := by linarith
    calc
      t ≤ t + 4 := by norm_num
      _ = 1 * (t + 4) := by ring
      _ ≤ (t + 1) ^ 2 * (t + 4) :=
        mul_le_mul_of_nonneg_right hone hright
      _ = firstOrderStationaryCubic (t + 1) := by
        unfold firstOrderStationaryCubic
        ring
  have htarget : t ∈ Set.Icc (firstOrderStationaryCubic 0)
      (firstOrderStationaryCubic (t + 1)) := by
    refine ⟨?_, hupper⟩
    simp [firstOrderStationaryCubic, ht.le]
  obtain ⟨u, hu, hut⟩ := Set.mem_image _ _ _ |>.mp
    (intermediate_value_Icc (show (0 : ℝ) ≤ t + 1 by positivity)
      (show ContinuousOn firstOrderStationaryCubic (Set.Icc 0 (t + 1)) by
        unfold firstOrderStationaryCubic
        fun_prop)
      htarget)
  refine ⟨u, ?_, hut⟩
  have hu0 : 0 ≤ u := hu.1
  rcases hu0.eq_or_lt with huZero | huPos
  · subst u
    simp [firstOrderStationaryCubic] at hut
    nlinarith
  · exact huPos

/-- The total stationary-root selector.  Only its positive-rate specification is used. -/
def firstOrderLowRateStationaryU (rho : ℝ) : ℝ :=
  if hrho : 0 < rho then Classical.choose (exists_firstOrderStationaryRoot hrho) else 0

theorem firstOrderLowRateStationaryU_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < firstOrderLowRateStationaryU rho := by
  rw [firstOrderLowRateStationaryU, dif_pos hrho]
  exact (Classical.choose_spec (exists_firstOrderStationaryRoot hrho)).1

theorem firstOrderLowRateStationaryU_cubic {rho : ℝ} (hrho : 0 < rho) :
    firstOrderStationaryCubic (firstOrderLowRateStationaryU rho) =
      firstOrderLowRateScale rho := by
  rw [firstOrderLowRateStationaryU, dif_pos hrho]
  exact (Classical.choose_spec (exists_firstOrderStationaryRoot hrho)).2

theorem firstOrderLowRateStationaryU_unique {rho u : ℝ}
    (hrho : 0 < rho) (hu : 0 ≤ u)
    (hcubic : firstOrderStationaryCubic u = firstOrderLowRateScale rho) :
    u = firstOrderLowRateStationaryU rho := by
  apply firstOrderStationaryCubic_strictMonoOn.injOn hu
    (firstOrderLowRateStationaryU_pos hrho).le
  rw [hcubic, firstOrderLowRateStationaryU_cubic hrho]

/-- Stationary derivative-degree ratio on the low-rate branch. -/
def firstOrderLowRateBeta (rho : ℝ) : ℝ :=
  firstOrderLowRateStationaryU rho / (2 * firstOrderLowRateScale rho)

/-- Low-rate branch of the first-order agreement threshold. -/
def firstOrderLowRateThreshold (rho : ℝ) : ℝ :=
  firstOrderLowRateScale rho + rho * firstOrderLowRateBeta rho

theorem firstOrderLowRateStationaryU_gt_scale {rho : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho) :
    firstOrderLowRateScale rho < firstOrderLowRateStationaryU rho := by
  let t := firstOrderLowRateScale rho
  let u := firstOrderLowRateStationaryU rho
  have ht : 0 < t := firstOrderLowRateScale_pos hrho
  have hu : 0 < u := firstOrderLowRateStationaryU_pos hrho
  have hcubic : firstOrderStationaryCubic u = t := by
    simpa only [u, t] using firstOrderLowRateStationaryU_cubic hrho
  have htt : firstOrderStationaryCubic t < t := by
    dsimp only [FirstOrderLowRateRegime, t] at hlow
    have hmul := mul_lt_mul_of_pos_left hlow ht
    unfold firstOrderStationaryCubic
    nlinarith
  by_contra hnot
  have hut : u ≤ t := le_of_not_gt hnot
  have hmono : firstOrderStationaryCubic u ≤ firstOrderStationaryCubic t :=
    firstOrderStationaryCubic_strictMonoOn.monotoneOn hu.le ht.le hut
  rw [hcubic] at hmono
  linarith

theorem firstOrderLowRateBeta_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < firstOrderLowRateBeta rho := by
  unfold firstOrderLowRateBeta
  positivity [firstOrderLowRateStationaryU_pos hrho, firstOrderLowRateScale_pos hrho]

theorem half_lt_firstOrderLowRateBeta {rho : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho) :
    1 / 2 < firstOrderLowRateBeta rho := by
  have ht := firstOrderLowRateScale_pos hrho
  have hu := firstOrderLowRateStationaryU_gt_scale hrho hlow
  unfold firstOrderLowRateBeta
  rw [lt_div_iff₀ (mul_pos (by norm_num) ht)]
  nlinarith

theorem firstOrderLowRateThreshold_eq_scale_mul_one_add {rho : ℝ} (hrho : 0 < rho) :
    firstOrderLowRateThreshold rho = firstOrderLowRateScale rho *
      (1 + firstOrderLowRateStationaryU rho) := by
  let t := firstOrderLowRateScale rho
  let u := firstOrderLowRateStationaryU rho
  have ht : 0 < t := firstOrderLowRateScale_pos hrho
  have htSq : t ^ 2 = rho / 2 := firstOrderLowRateScale_sq hrho.le
  have hrhoEq : rho = 2 * t ^ 2 := by nlinarith [htSq]
  change t + rho * (u / (2 * t)) = t * (1 + u)
  rw [hrhoEq]
  field_simp [ne_of_gt ht]

/-- On the low stationary branch the agreement threshold remains strictly above capacity. -/
theorem rate_lt_firstOrderLowRateThreshold {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : FirstOrderLowRateRegime rho) :
    rho < firstOrderLowRateThreshold rho := by
  let t := firstOrderLowRateScale rho
  let u := firstOrderLowRateStationaryU rho
  have ht : 0 < t := firstOrderLowRateScale_pos hrho
  have htSq : t ^ 2 = rho / 2 := firstOrderLowRateScale_sq hrho.le
  have htOne : t < 1 := by nlinarith [sq_nonneg (t - 1)]
  have hu : t < u := by
    simpa only [t, u] using firstOrderLowRateStationaryU_gt_scale hrho hlow
  have ha : firstOrderLowRateThreshold rho = t * (1 + u) := by
    simpa only [t, u] using firstOrderLowRateThreshold_eq_scale_mul_one_add hrho
  rw [ha]
  nlinarith [mul_pos ht (sub_pos.mpr hu)]

theorem firstOrderLowRateBeta_lt_threshold_div_rate {rho : ℝ} (hrho : 0 < rho) :
    firstOrderLowRateBeta rho < firstOrderLowRateThreshold rho / rho := by
  rw [lt_div_iff₀ hrho]
  unfold firstOrderLowRateThreshold
  have ht := firstOrderLowRateScale_pos hrho
  linarith

/-- The stationary threshold has zero source-minus-rank margin on the low-rate branch. -/
theorem firstOrderLowRate_margin_eq_zero {rho : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho) :
    firstOrderSourceDensity rho (firstOrderLowRateThreshold rho)
        (firstOrderLowRateBeta rho) -
      firstOrderRankDensity (firstOrderLowRateBeta rho) = 0 := by
  let t := firstOrderLowRateScale rho
  let u := firstOrderLowRateStationaryU rho
  let beta := firstOrderLowRateBeta rho
  have ht : 0 < t := firstOrderLowRateScale_pos hrho
  have htSq : t ^ 2 = rho / 2 := firstOrderLowRateScale_sq hrho.le
  have hrhoEq : rho = 2 * t ^ 2 := by nlinarith [htSq]
  have huEq : u ^ 2 * (u + 3) = t := by
    simpa only [firstOrderStationaryCubic, u, t] using
      firstOrderLowRateStationaryU_cubic hrho
  have hbeta : beta = u / (2 * t) := rfl
  have hbeta' : firstOrderLowRateBeta rho = u / (2 * t) := hbeta
  have ha : firstOrderLowRateThreshold rho = t * (1 + u) := by
    simpa only [t, u] using firstOrderLowRateThreshold_eq_scale_mul_one_add hrho
  have hhalf : ¬ beta ≤ 1 / 2 := not_le.mpr (by
    simpa only [beta] using half_lt_firstOrderLowRateBeta hrho hlow)
  have hsource :
      firstOrderSourceDensity rho (firstOrderLowRateThreshold rho)
          (firstOrderLowRateBeta rho) =
        u * (u ^ 2 + 3 * u + 3) / (24 * t) := by
    rw [firstOrderSourceDensity, ha, hbeta', hrhoEq]
    field_simp [ne_of_gt ht]
    ring
  have hrank :
      firstOrderRankDensity (firstOrderLowRateBeta rho) =
        (3 * u + t) / (24 * t) := by
    rw [firstOrderRankDensity, if_neg hhalf, hbeta']
    field_simp [ne_of_gt ht]
    ring
  rw [hsource, hrank]
  field_simp [ne_of_gt ht]
  nlinarith [huEq]

/-- Exact positive-margin factorization above the low-rate threshold. -/
theorem firstOrderLowRate_margin_factor {rho a : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho) :
    firstOrderSourceDensity rho a (firstOrderLowRateBeta rho) -
        firstOrderRankDensity (firstOrderLowRateBeta rho) =
      firstOrderLowRateBeta rho / 2 *
        (a - firstOrderLowRateThreshold rho) *
        ((a + firstOrderLowRateThreshold rho) / rho -
          firstOrderLowRateBeta rho) := by
  have hzero := firstOrderLowRate_margin_eq_zero hrho hlow
  rw [firstOrderSourceDensity] at hzero ⊢
  field_simp [ne_of_gt hrho] at hzero ⊢
  nlinarith

theorem firstOrderLowRate_margin_pos {rho a : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho)
    (ha : firstOrderLowRateThreshold rho < a) :
    0 < firstOrderSourceDensity rho a (firstOrderLowRateBeta rho) -
      firstOrderRankDensity (firstOrderLowRateBeta rho) := by
  rw [firstOrderLowRate_margin_factor hrho hlow]
  have hbeta := firstOrderLowRateBeta_pos hrho
  have hratio := firstOrderLowRateBeta_lt_threshold_div_rate hrho
  have hbracket : 0 < (a + firstOrderLowRateThreshold rho) / rho -
      firstOrderLowRateBeta rho := by
    have hthresholdPos : 0 < firstOrderLowRateThreshold rho := by
      unfold firstOrderLowRateThreshold
      exact add_pos (firstOrderLowRateScale_pos hrho)
        (mul_pos hrho (firstOrderLowRateBeta_pos hrho))
    have : firstOrderLowRateBeta rho <
        (a + firstOrderLowRateThreshold rho) / rho := by
      apply hratio.trans
      gcongr
      linarith
    linarith
  exact mul_pos (mul_pos (half_pos hbeta) (sub_pos.mpr ha)) hbracket

end

end ReedSolomon.HiddenDerivative
