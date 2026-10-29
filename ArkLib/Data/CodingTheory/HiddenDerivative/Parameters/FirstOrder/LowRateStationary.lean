/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RateBound
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The stationary root on the low-rate first-order branch

`ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RateBound` tunes the first-order
support with the ratio `β = 3(1 - a)/(2(2 - R))`, chosen against the cubic envelope of the rank
density. For small rates the exact rank density `β/4 + 1/24` (for `β > 1/2`) gives a better
threshold. With `t = √(ρ/2)`, the stationary choice is the unique positive root `u` of

```text
u² (u + 3) = t,        β = u / (2t),        a = t + ρ β = t (1 + u).
```

At that threshold the source density equals the exact rank density, and above it the source
density is strictly larger. The branch condition is the intrinsic inequality `t (t + 3) < 1`,
which forces `u > t` and hence `β > 1/2`; it is equivalent to `ρ < 11 - 3√13`.

## Main statements

* `firstOrderLowRateRegime_iff_lt_rateSwitch`: `t (t + 3) < 1 ↔ ρ < 11 - 3√13` for every `ρ`.
* `exists_firstOrderStationaryRoot`, `firstOrderLowRateStationaryU_cubic`,
  `firstOrderLowRateStationaryU_unique`: the positive root exists and is unique.
* `half_lt_firstOrderLowRateBeta`, `rate_lt_firstOrderLowRateThreshold`: on the branch,
  `β > 1/2` and `ρ < a`.
* `firstOrderLowRate_margin_eq_zero`, `firstOrderLowRate_margin_factor`,
  `firstOrderLowRate_margin_pos`: the source-minus-rank margin vanishes at the threshold,
  factors as `(β/2)(a - a*)((a + a*)/ρ - β)`, and is positive for `a > a*`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section


/-- The cubic `u² (u + 3)`. It is strictly increasing on `[0, ∞)` and its inverse there defines
the low-rate stationary parameter. -/
def firstOrderStationaryCubic (u : ℝ) : ℝ := u ^ 2 * (u + 3)

/-- The scale `t = √(ρ/2)` of the stationary equations. For `ρ < 0` it is `0`. -/
def firstOrderLowRateScale (rho : ℝ) : ℝ := Real.sqrt (rho / 2)

/-- The rate `11 - 3√13 ≈ 0.183` at which the stationary ratio `β` reaches `1/2`. -/
def firstOrderRateSwitch : ℝ := 11 - 3 * Real.sqrt 13

/-- The open low-rate branch condition `t (t + 3) < 1` with `t = √(ρ/2)`. -/
def FirstOrderLowRateRegime (rho : ℝ) : Prop :=
  firstOrderLowRateScale rho * (firstOrderLowRateScale rho + 3) < 1

/-- `t > 0` for `ρ > 0`. -/
theorem firstOrderLowRateScale_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < firstOrderLowRateScale rho := by
  unfold firstOrderLowRateScale
  exact Real.sqrt_pos.2 (by positivity)

/-- `t² = ρ/2` for `ρ ≥ 0`. For `ρ < 0` the left side is `0`. -/
theorem firstOrderLowRateScale_sq {rho : ℝ} (hrho : 0 ≤ rho) :
    firstOrderLowRateScale rho ^ 2 = rho / 2 := by
  unfold firstOrderLowRateScale
  exact Real.sq_sqrt (by positivity)

/-- The branch condition is equivalent to `ρ < 11 - 3√13`. For `ρ < 0` both sides hold: `t = 0`
and `11 - 3√13 > 0`. -/
theorem firstOrderLowRateRegime_iff_lt_rateSwitch (rho : ℝ) :
    FirstOrderLowRateRegime rho ↔ rho < firstOrderRateSwitch := by
  rcases lt_or_ge rho 0 with hneg | hrho
  · have hscale : firstOrderLowRateScale rho = 0 :=
      Real.sqrt_eq_zero'.2 (by linarith)
    have hr : Real.sqrt 13 < 11 / 3 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    simp only [FirstOrderLowRateRegime, hscale, firstOrderRateSwitch]
    constructor <;> intro _ <;> linarith
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
    calc
      ((r - 3) / 2) ^ 2 = (r ^ 2 - 6 * r + 9) / 4 := by ring
      _ = (11 - 3 * r) / 2 := by rw [hrSq]; ring
  have hbBoundary : b * (b + 3) = 1 := by
    dsimp only [b]
    calc
      ((r - 3) / 2) * ((r - 3) / 2 + 3) = (r ^ 2 - 9) / 4 := by ring
      _ = 1 := by rw [hrSq]; norm_num
  have hbranch : t * (t + 3) < 1 ↔ t < b := by
    have hfactor : 0 < t + b + 3 := by positivity
    have hidentity : t * (t + 3) - 1 = (t - b) * (t + b + 3) := by
      rw [← hbBoundary]
      ring
    constructor
    · intro h
      have hprod : (t - b) * (t + b + 3) < 0 := by
        rw [← hidentity]
        linarith
      by_contra hnot
      have hnonneg : 0 ≤ (t - b) * (t + b + 3) :=
        mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) hfactor.le
      linarith
    · intro htb
      have hprod : (t - b) * (t + b + 3) < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr htb) hfactor
      rw [← hidentity] at hprod
      linarith
  change t * (t + 3) < 1 ↔ rho < firstOrderRateSwitch
  rw [hbranch]
  rw [← sq_lt_sq₀ ht0 hb0, htSq, hbSq]
  constructor <;> intro h <;> linarith

/-- The cubic `u² (u + 3)` is strictly increasing on `[0, ∞)`. -/
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

/-- For `ρ > 0` the equation `u² (u + 3) = t` has a positive solution, by the intermediate value
theorem on `[0, t + 1]`. -/
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

/-- The stationary root: the positive solution of `u² (u + 3) = t` for `ρ > 0`, and `0` otherwise.
-/
def firstOrderLowRateStationaryU (rho : ℝ) : ℝ :=
  if hrho : 0 < rho then Classical.choose (exists_firstOrderStationaryRoot hrho) else 0

/-- The stationary root is positive for `ρ > 0`. -/
theorem firstOrderLowRateStationaryU_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < firstOrderLowRateStationaryU rho := by
  rw [firstOrderLowRateStationaryU, dite_eq_left_of_eq_true (eq_true hrho)]
  exact (Classical.choose_spec (exists_firstOrderStationaryRoot hrho)).1

/-- The stationary root solves `u² (u + 3) = t` for `ρ > 0`. -/
theorem firstOrderLowRateStationaryU_cubic {rho : ℝ} (hrho : 0 < rho) :
    firstOrderStationaryCubic (firstOrderLowRateStationaryU rho) =
      firstOrderLowRateScale rho := by
  rw [firstOrderLowRateStationaryU, dite_eq_left_of_eq_true (eq_true hrho)]
  exact (Classical.choose_spec (exists_firstOrderStationaryRoot hrho)).2

/-- Every nonnegative solution of `u² (u + 3) = t` is the stationary root. -/
theorem firstOrderLowRateStationaryU_unique {rho u : ℝ}
    (hrho : 0 < rho) (hu : 0 ≤ u)
    (hcubic : firstOrderStationaryCubic u = firstOrderLowRateScale rho) :
    u = firstOrderLowRateStationaryU rho := by
  apply firstOrderStationaryCubic_strictMonoOn.injOn hu
    (firstOrderLowRateStationaryU_pos hrho).le
  rw [hcubic, firstOrderLowRateStationaryU_cubic hrho]

/-- The stationary derivative-degree ratio `β = u / (2t)`. -/
def firstOrderLowRateBeta (rho : ℝ) : ℝ :=
  firstOrderLowRateStationaryU rho / (2 * firstOrderLowRateScale rho)

/-- The low-rate first-order agreement threshold `a* = t + ρ β`. -/
def firstOrderLowRateThreshold (rho : ℝ) : ℝ :=
  firstOrderLowRateScale rho + rho * firstOrderLowRateBeta rho

/-- On the branch, `t < u`: the branch condition says `t² (t + 3) < t`, so the increasing cubic
reaches `t` only after `t`. -/
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

/-- `β > 0` for `ρ > 0`. -/
theorem firstOrderLowRateBeta_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < firstOrderLowRateBeta rho := by
  unfold firstOrderLowRateBeta
  positivity [firstOrderLowRateStationaryU_pos hrho, firstOrderLowRateScale_pos hrho]

/-- On the branch, `β > 1/2`, so the exact rank density is on its linear piece. -/
theorem half_lt_firstOrderLowRateBeta {rho : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho) :
    1 / 2 < firstOrderLowRateBeta rho := by
  have ht := firstOrderLowRateScale_pos hrho
  have hu := firstOrderLowRateStationaryU_gt_scale hrho hlow
  unfold firstOrderLowRateBeta
  rw [lt_div_iff₀ (mul_pos (by norm_num) ht)]
  nlinarith

/-- `a* = t (1 + u)` for `ρ > 0`. -/
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

/-- On the branch, `ρ < a*`. The branch condition gives `t < 1/3`, so no bound `ρ < 1` is
needed. -/
theorem rate_lt_firstOrderLowRateThreshold {rho : ℝ}
    (hrho : 0 < rho) (hlow : FirstOrderLowRateRegime rho) :
    rho < firstOrderLowRateThreshold rho := by
  let t := firstOrderLowRateScale rho
  let u := firstOrderLowRateStationaryU rho
  have ht : 0 < t := firstOrderLowRateScale_pos hrho
  have htSq : t ^ 2 = rho / 2 := firstOrderLowRateScale_sq hrho.le
  have htOne : t < 1 := by
    have : t * (t + 3) < 1 := hlow
    nlinarith
  have hu : t < u := by
    simpa only [t, u] using firstOrderLowRateStationaryU_gt_scale hrho hlow
  have ha : firstOrderLowRateThreshold rho = t * (1 + u) := by
    simpa only [t, u] using firstOrderLowRateThreshold_eq_scale_mul_one_add hrho
  rw [ha]
  nlinarith [mul_pos ht (sub_pos.mpr hu)]

/-- `β < a* / ρ` for `ρ > 0`, since `a* - ρ β = t > 0`. -/
theorem firstOrderLowRateBeta_lt_threshold_div_rate {rho : ℝ} (hrho : 0 < rho) :
    firstOrderLowRateBeta rho < firstOrderLowRateThreshold rho / rho := by
  rw [lt_div_iff₀ hrho]
  unfold firstOrderLowRateThreshold
  have ht := firstOrderLowRateScale_pos hrho
  linarith

/-- On the branch, the source density at the threshold equals the exact rank density at `β`. -/
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
    rw [firstOrderRankDensity]
    split_ifs with hle
    · exact absurd hle hhalf
    rw [hbeta']
    field_simp [ne_of_gt ht]
    ring
  rw [hsource, hrank]
  field_simp [ne_of_gt ht]
  nlinarith [huEq]

/-- On the branch, the margin at agreement `a` factors as `(β/2)(a - a*)((a + a*)/ρ - β)`. -/
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

/-- On the branch, the source density strictly exceeds the exact rank density for every
`a > a*`. -/
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
