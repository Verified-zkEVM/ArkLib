/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.BranchwiseRate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.FiniteRateParameters
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridRateEnvelope
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageComparison
import Mathlib.Order.Interval.Finset.Nat

/-!
# First-order parameter acceptance tests

Small concrete checks for the first-order rate bounds, hybrid constants, rounded counts and curve
charges.
-/

namespace ReedSolomon.HiddenDerivative

open Filter Topology

private theorem rateSwitch_lt_half : firstOrderRateSwitch < 1 / 2 := by
  have h : (7 : ℝ) < 2 * Real.sqrt 13 := by
    have h13 : (7 / 2 : ℝ) < Real.sqrt 13 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  unfold firstOrderRateSwitch
  linarith

private theorem half_rate_threshold_lt_three_four :
    firstOrderRateThreshold (1 / 2) < 3 / 4 := by
  refine (firstOrderRateThreshold_lt_sqrt (by norm_num) (by norm_num)).trans ?_
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

private theorem lowRate_eighth_regime : FirstOrderLowRateRegime (1 / 8) := by
  rw [firstOrderLowRateRegime_iff_lt_rateSwitch, firstOrderRateSwitch]
  have hsqrt : Real.sqrt 13 < 29 / 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

private theorem concrete_rate_ratio : firstOrderRateBeta (1 / 2) (3 / 4) = 1 / 4 := by
  norm_num [firstOrderRateBeta]

/-! ### Rate bounds and branch selection -/

/-- At `R = 1/2`, `a = 3/4`, the chosen ratio is `1/4`. -/
example : firstOrderBranchBeta (1 / 2) (3 / 4) = 1 / 4 := by
  rw [firstOrderBranchBeta_eq_clean rateSwitch_lt_half.le, firstOrderRateBeta]
  norm_num

/-- At `R = 1/2`, the threshold lies strictly between `R` and `√R`. -/
example : (1 / 2 : ℝ) < firstOrderRateThreshold (1 / 2) ∧
    firstOrderRateThreshold (1 / 2) < Real.sqrt (1 / 2) := by
  exact ⟨rate_lt_firstOrderRateThreshold (by norm_num) (by norm_num),
    firstOrderRateThreshold_lt_sqrt (by norm_num) (by norm_num)⟩

/-- The clean expression is above one at `R = 1/2`, `a = 3/4`. -/
example : 1 < firstOrderCleanExpression (1 / 2) (3 / 4) :=
  firstOrderCleanExpression_gt_one (by norm_num) (by norm_num)
    half_rate_threshold_lt_three_four

/-- The exact rank density is below its cubic envelope at `β = 3/4`. -/
example : firstOrderRankDensity (3 / 4) ≤ firstOrderRankCubicEnvelope (3 / 4) :=
  firstOrderRankDensity_le_cubicEnvelope (3 / 4)

/-- The threshold equation holds at `R = 1/2`. -/
example : firstOrderCleanExpression (1 / 2) (firstOrderRateThreshold (1 / 2)) = 1 :=
  firstOrderCleanExpression_threshold_eq_one (by norm_num) (by norm_num)

/-- Below the branch switch, the stationary root gives `β > 1/2` and `ρ < a`. -/
example : FirstOrderLowRateRegime (1 / 10) ∧ 1 / 2 < firstOrderLowRateBeta (1 / 10) ∧
    (1 / 10 : ℝ) < firstOrderLowRateThreshold (1 / 10) := by
  have hlow : FirstOrderLowRateRegime (1 / 10) := by
    rw [firstOrderLowRateRegime_iff_lt_rateSwitch, firstOrderRateSwitch]
    have h : Real.sqrt 13 < 109 / 30 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  exact ⟨hlow, half_lt_firstOrderLowRateBeta (by norm_num) hlow,
    rate_lt_firstOrderLowRateThreshold (by norm_num) hlow⟩

/-- At rate `1/8`, both branch definitions select the stationary branch with positive ratio. -/
example : firstOrderBranchThreshold (1 / 8) = firstOrderLowRateThreshold (1 / 8) ∧
    firstOrderBranchBeta (1 / 8) (3 / 4) = firstOrderLowRateBeta (1 / 8) ∧
    0 < firstOrderBranchBeta (1 / 8) (3 / 4) := by
  have hlow : (1 / 8 : ℝ) < firstOrderRateSwitch :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch _).mp lowRate_eighth_regime
  exact ⟨firstOrderBranchThreshold_eq_low hlow, firstOrderBranchBeta_eq_low hlow,
    firstOrderBranchBeta_pos (by norm_num) (by norm_num) (by norm_num)⟩

/-- At rate `1/8` and agreement `1`, the low-rate source-minus-rank margin is positive. -/
example : 0 < firstOrderSourceDensity (1 / 8) 1 (firstOrderLowRateBeta (1 / 8)) -
    firstOrderRankDensity (firstOrderLowRateBeta (1 / 8)) := by
  apply firstOrderLowRate_margin_pos (by norm_num) lowRate_eighth_regime
  have ht : firstOrderLowRateScale (1 / 8) = 1 / 4 := by
    rw [firstOrderLowRateScale,
      show (1 / 8 : ℝ) / 2 = (1 / 4 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : 0 ≤ (1 / 4 : ℝ))]
  have hu : firstOrderLowRateStationaryU (1 / 8) < 1 := by
    by_contra h
    have hge : 1 ≤ firstOrderLowRateStationaryU (1 / 8) := le_of_not_gt h
    have hc := firstOrderLowRateStationaryU_cubic (rho := (1 / 8 : ℝ)) (by norm_num)
    rw [ht] at hc
    unfold firstOrderStationaryCubic at hc
    have hbound : 4 ≤ firstOrderLowRateStationaryU (1 / 8) ^ 2 *
        (firstOrderLowRateStationaryU (1 / 8) + 3) := by
      calc
        4 = (1 : ℝ) ^ 2 * (1 + 3) := by norm_num
        _ ≤ firstOrderLowRateStationaryU (1 / 8) ^ 2 *
            (firstOrderLowRateStationaryU (1 / 8) + 3) := by gcongr
    linarith
  rw [firstOrderLowRateThreshold_eq_scale_mul_one_add (by norm_num), ht]
  nlinarith [hu]

/-- At rate `1/8`, the positive stationary root exists and is the unique nonnegative root. -/
example : ∃ u : ℝ, 0 < u ∧
    firstOrderStationaryCubic u = firstOrderLowRateScale (1 / 8) ∧
    firstOrderStationaryCubic (firstOrderLowRateStationaryU (1 / 8)) =
      firstOrderLowRateScale (1 / 8) ∧
    u = firstOrderLowRateStationaryU (1 / 8) := by
  obtain ⟨u, hu, hcubic⟩ := exists_firstOrderStationaryRoot (rho := (1 / 8 : ℝ)) (by norm_num)
  exact ⟨u, hu, hcubic, firstOrderLowRateStationaryU_cubic (by norm_num),
    firstOrderLowRateStationaryU_unique (by norm_num) hu.le hcubic⟩

/-- The source-minus-envelope factorization at the chosen rate ratio. -/
example :
    firstOrderSourceDensity (1 / 2) (3 / 4) (firstOrderRateBeta (1 / 2) (3 / 4)) -
        firstOrderRankCubicEnvelope (firstOrderRateBeta (1 / 2) (3 / 4)) =
      firstOrderRateBeta (1 / 2) (3 / 4) / 2 *
        (firstOrderCleanExpression (1 / 2) (3 / 4) - 1) := by
  rw [firstOrderSourceDensity_sub_cubicEnvelope _ _ _ (by norm_num),
    firstOrderRateBeta_bracket _ _ (by norm_num) (by norm_num)]

/-- The piecewise ratio at `R = 1/2` lies below `a/R` when `a = 3/4`. -/
example : firstOrderBranchBeta (1 / 2) (3 / 4) < (3 / 4) / (1 / 2) := by
  have ha : firstOrderBranchThreshold (1 / 2) < 3 / 4 := by
    rw [firstOrderBranchThreshold_eq_clean rateSwitch_lt_half.le]
    exact half_rate_threshold_lt_three_four
  exact firstOrderBranchBeta_lt_agreement_div_rate (by norm_num) (by norm_num) ha

/-- The piecewise density surplus is positive at `R = 1/2`, `a = 3/4`. -/
example : firstOrderRankDensity (firstOrderBranchBeta (1 / 2) (3 / 4)) <
    firstOrderSourceDensity (1 / 2) (3 / 4) (firstOrderBranchBeta (1 / 2) (3 / 4)) :=
  firstOrderBranch_surplus_pos (by norm_num) (by norm_num)
    (by rw [firstOrderBranchThreshold_eq_clean rateSwitch_lt_half.le];
        exact half_rate_threshold_lt_three_four) (by norm_num)

/-! ### Rounded counts -/

/-- The derivative-order-one certified bound is `5` for multiplicity `2`, cap `1`. -/
example : certifiedEnlargedRankBound 1 2 1 0 = 5 := by
  rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount]
  decide

/-- The signed cubic count bounds the rank count at multiplicity `2`, cap `1`. -/
example : (firstOrderRankCount 2 1 : ℝ) ≤ firstOrderRankCubicUpperCount 2 1 :=
  firstOrderRankCount_le_cubicUpperCount 2 1

/-- The rounded rank estimate at `m = 4`, `β = 1/2`. -/
example : (firstOrderRankCount 4 ⌊(1 / 2 : ℝ) * 4⌋₊ : ℝ) ≤
    (4 : ℝ) ^ 3 * ((1 / 2 : ℝ) / 2 - (1 / 2) ^ 2 / 2 + (1 / 2) ^ 3 / 3) + 3 * 4 ^ 2 :=
  firstOrderRankCount_floor_le 4 (by norm_num) (by norm_num)

/-- At `m = 4` and `β = 1`, the exact upper-branch rank density gives `35 ≤ 4³ + 5·4²`. -/
example : ((35 : ℕ) : ℝ) ≤
    (4 : ℕ) ^ 3 * firstOrderRankDensity 1 + (2 * 1 + 3) * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le_density_add_rounding_upper
    (beta := 1) (by norm_num) 4
  have hM : ⌊(1 : ℝ) * (4 : ℕ)⌋₊ = 4 := by norm_num
  have hcount : firstOrderRankCount 4 4 = 35 := by decide
  rw [hM, hcount] at h
  norm_num [firstOrderRankDensity] at h ⊢

/-- At the branch boundary, the uniform rank estimate gives `23 ≤ 4³/6 + 4²·4`. -/
example : ((23 : ℕ) : ℝ) ≤
    (4 : ℕ) ^ 3 * firstOrderRankDensity (1 / 2) + (2 * (1 / 2) + 3) * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le_density_add_rounding
    (beta := 1 / 2) (by norm_num) 4
  have hM : ⌊(1 / 2 : ℝ) * (4 : ℕ)⌋₊ = 2 := by norm_num
  rw [hM, show firstOrderRankCount 4 2 = 23 by decide] at h
  norm_num [firstOrderRankDensity] at h ⊢

/-- At `R = 1/2`, `a = 1`, `β = 1/4`, `m = 64`, both rounding and finite-surplus bounds hold. -/
example :
    (64 : ℝ) ^ 3 * ((1 / 4 : ℝ) * 1 ^ 2 / (2 * (1 / 2)) -
      1 * (1 / 4) ^ 2 / 2 + (1 / 2) * (1 / 4) ^ 3 / 6) ≤
      firstOrderSourceCount (1 / 2) 1 64 ⌊(1 / 4 : ℝ) * 64⌋₊ 128 ∧
    (64 : ℝ) ^ 3 * (((1 / 4 : ℝ) * 1 ^ 2 / (2 * (1 / 2)) -
      1 * (1 / 4) ^ 2 / 2 + (1 / 2) * (1 / 4) ^ 3 / 6) -
      ((1 / 4 : ℝ) / 2 - (1 / 4) ^ 2 / 2 + (1 / 4) ^ 3 / 3)) - 3 * 64 ^ 2 ≤
      firstOrderSourceCount (1 / 2) 1 64 ⌊(1 / 4 : ℝ) * 64⌋₊ 128 -
        firstOrderRankCount 64 ⌊(1 / 4 : ℝ) * 64⌋₊ := by
  exact ⟨cube_mul_sourceDensity_le_firstOrderSourceCount (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    cube_mul_densityGap_sub_le_sourceCount_sub_rankCount (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

private noncomputable def roundedSourcePolynomial (m M L : ℕ) : ℝ :=
  3 * (m : ℝ) * (M + 1) * (M + 2) / 8 -
    (M : ℝ) * (M + 1) * (M + 2) / 6 +
    (M + 1) * ((L - M : ℕ) * (3 * (m : ℝ) / 4) -
      ((L : ℝ) * (L + 1) - (M : ℝ) * (M + 1)) / 4)

private noncomputable def roundedRankPolynomial (m M : ℕ) : ℝ :=
  (M + 1) * (m : ℝ) * (m + 1) / 2 -
    ((m - 2 * M + 1 : ℕ) : ℝ) * M * (M + 1) / 2 -
    2 * (M : ℝ) * (M - 1) * (M + 1) / 3

private noncomputable def roundedSourceModel (p : (ℝ × ℝ) × ℝ) : ℝ :=
  let x := p.1.1
  let y := p.1.2
  let e := p.2
  3 / 8 * (x + e) * (x + 2 * e) -
    x * (x + e) * (x + 2 * e) / 6 +
    (x + e) * (3 / 4 * (y - x) - (y * (y + e) - x * (x + e)) / 4)

private noncomputable def roundedRankModel (p : ℝ × ℝ) : ℝ :=
  let x := p.1
  let e := p.2
  (x + e) * (1 + e) / 2 -
    (1 - 2 * x + e) * x * (x + e) / 2 - 2 * x * (x - e) * (x + e) / 3

private theorem sum_range_cast_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
  rw [eq_div_iff two_ne_zero, Finset.sum_range_natCast_mul_two]

private theorem sum_range_cast_sq_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) =
      (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  rw [eq_div_iff (by norm_num : (6 : ℝ) ≠ 0), Finset.sum_range_natCast_sq_mul_six]

private theorem roundedSourceCount_eq_polynomial {m : ℕ} (hm : 0 < m) :
    firstOrderSourceCount (1 / 2) (3 / 4) m
      (firstOrderRateDerivativeCap (1 / 2) (3 / 4) m)
      (firstOrderRateJetDegree (1 / 2) (3 / 4) m) =
        roundedSourcePolynomial m ⌊(1 / 4 : ℝ) * m⌋₊ ⌊(3 / 2 : ℝ) * m⌋₊ := by
  let M := ⌊(1 / 4 : ℝ) * m⌋₊
  let L := ⌊(3 / 2 : ℝ) * m⌋₊
  have hMcap : firstOrderRateDerivativeCap (1 / 2) (3 / 4) m = M := by
    norm_num [M, firstOrderRateDerivativeCap, firstOrderRateBeta]
  have hLcap : firstOrderRateJetDegree (1 / 2) (3 / 4) m = ⌈(3 / 2 : ℝ) * m⌉₊ := by
    simp [firstOrderRateJetDegree]
    ring_nf
  have hML : M ≤ L := by
    apply Nat.floor_mono
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  have hMle : 2 * M ≤ m := by
    have hMreal : (M : ℝ) ≤ (1 / 4 : ℝ) * m :=
      Nat.floor_le (show (0 : ℝ) ≤ (1 / 4 : ℝ) * m by positivity)
    exact_mod_cast (by nlinarith [hMreal] : 2 * (M : ℝ) ≤ (m : ℝ))
  have hLreal : (L : ℝ) ≤ (3 / 2 : ℝ) * m :=
    Nat.floor_le (by positivity)
  have hceilLo : L ≤ ⌈(3 / 2 : ℝ) * m⌉₊ := Nat.floor_le_ceil _
  have hceilHi : ⌈(3 / 2 : ℝ) * m⌉₊ ≤ L + 1 := Nat.ceil_le_floor_add_one _
  have hceilRange :
      (∑ t ∈ Finset.range (⌈(3 / 2 : ℝ) * m⌉₊ + 1),
        (min t M + 1 : ℕ) * max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0) =
        ∑ t ∈ Finset.range (L + 1),
          (min t M + 1 : ℕ) * max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0 := by
    by_cases h : ⌈(3 / 2 : ℝ) * m⌉₊ = L
    · rw [h]
    · have h' : ⌈(3 / 2 : ℝ) * m⌉₊ = L + 1 := by omega
      rw [h', Finset.sum_range_succ]
      have htail : (3 / 2 : ℝ) * m < (L : ℝ) + 1 := Nat.lt_floor_add_one _
      have hneg : m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * (L + 1) < 0 := by
        linarith [htail]
      have hneg' : m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * ((L + 1 : ℕ) : ℝ) < 0 := by
        simpa using hneg
      rw [max_eq_right hneg'.le]
      simp only [mul_zero, add_zero]
  have hres {t : ℕ} (ht : t ≤ L) :
      0 ≤ m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t := by
    have htR : (t : ℝ) ≤ L := by exact_mod_cast ht
    nlinarith
  have hfirst :
      (∑ t ∈ Finset.range (M + 1), (min t M + 1 : ℕ) *
        max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0) =
        3 * (m : ℝ) * (M + 1) * (M + 2) / 8 -
          (M : ℝ) * (M + 1) * (M + 2) / 6 := by
    have hsum1 (n : ℕ) :
        (∑ t ∈ Finset.range n, ((t : ℝ) + 1)) =
          (n : ℝ) * (n - 1) / 2 + n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, sum_range_cast_eq]
    have hsumt2 (n : ℕ) :
        (∑ t ∈ Finset.range n, ((t : ℝ) ^ 2 + t)) =
          (n : ℝ) * (n - 1) * (2 * n - 1) / 6 + (n : ℝ) * (n - 1) / 2 := by
      rw [Finset.sum_add_distrib, sum_range_cast_sq_eq, sum_range_cast_eq]
    calc
      _ = ∑ t ∈ Finset.range (M + 1),
          ((3 * (m : ℝ) / 4) * ((t : ℝ) + 1) -
            (1 / 2 : ℝ) * ((t : ℝ) ^ 2 + t)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htM : t ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
        rw [min_eq_left htM, max_eq_left (hres (Nat.le_trans htM hML))]
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1, hsumt2]
        push_cast
        ring
  have htail :
      (∑ t ∈ Finset.Ico (M + 1) (L + 1), (min t M + 1 : ℕ) *
        max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0) =
        (M + 1) * ((L - M : ℕ) * (3 * (m : ℝ) / 4) -
          ((L : ℝ) * (L + 1) - (M : ℝ) * (M + 1)) / 4) := by
    have hsumIco : (∑ t ∈ Finset.Ico (M + 1) (L + 1), (t : ℝ)) =
        ((L : ℝ) * L / 2 + L / 2) - ((M : ℝ) * M / 2 + M / 2) := by
      rw [Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hML), sum_range_cast_eq,
        sum_range_cast_eq]
      push_cast
      ring
    calc
      _ = ∑ t ∈ Finset.Ico (M + 1) (L + 1),
          ((M + 1 : ℝ) * (3 * (m : ℝ) / 4 - (1 / 2 : ℝ) * t)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htmem := Finset.mem_Ico.mp ht
        have htM : M ≤ t := by omega
        have htL : t ≤ L := by omega
        rw [min_eq_right htM, max_eq_left (hres htL)]
        push_cast
        ring
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico,
          nsmul_eq_mul, ← Finset.mul_sum, hsumIco]
        rw [show L + 1 - (M + 1) = L - M by omega]
        ring
  rw [firstOrderSourceCount, hMcap, hLcap, hceilRange,
    ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hML), hfirst, htail]
  rfl

private theorem roundedRankCount_eq_polynomial {m : ℕ} (hm : 0 < m) :
    (firstOrderRankCount m ⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) =
      roundedRankPolynomial m ⌊(1 / 4 : ℝ) * m⌋₊ := by
  let M := ⌊(1 / 4 : ℝ) * m⌋₊
  have hMle : 2 * M ≤ m := by
    have hMreal : (M : ℝ) ≤ (1 / 4 : ℝ) * m :=
      Nat.floor_le (show (0 : ℝ) ≤ (1 / 4 : ℝ) * m by positivity)
    exact_mod_cast (by nlinarith [hMreal] : 2 * (M : ℝ) ≤ (m : ℝ))
  have hformula : (firstOrderRankCount m M : ℝ) =
      (M + 1) * (m : ℝ) * (m + 1) / 2 -
        ((m - 2 * M + 1 : ℕ) : ℝ) * M * (M + 1) / 2 -
        2 * (M : ℝ) * (M - 1) * (M + 1) / 3 := by
    have hcast : (firstOrderRankCount m M : ℝ) =
        ∑ s ∈ Finset.range m,
          (((s + 1 : ℕ) : ℝ) * (M + 1) -
            ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
      unfold firstOrderRankCount
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs : s < m := Finset.mem_range.mp hs
      have hsub : (2 * s + 1 - m) * (s + M + 1 - m) ≤ (s + 1) * (M + 1) := by
        apply Nat.mul_le_mul <;> omega
      rw [Nat.cast_sub hsub]
      push_cast
      rfl
    have hamb :
        (∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) =
          (M + 1) * (m : ℝ) * (m + 1) / 2 := by
      have hsum : (∑ s ∈ Finset.range m, ((s : ℝ) + 1)) =
          (m : ℝ) * (m - 1) / 2 + m := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one, sum_range_cast_eq]
      calc
        _ = (∑ s ∈ Finset.range m, ((s : ℝ) + 1)) * (M + 1) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          push_cast
          ring
        _ = _ := by rw [hsum]; ring
    have hcorr :
        (∑ s ∈ Finset.range m,
          ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) =
          ((m : ℝ) - 2 * M + 1) * M * (M + 1) / 2 +
            2 * (M : ℝ) * (M - 1) * (M + 1) / 3 := by
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le m M)]
      have hprefix :
          (∑ s ∈ Finset.range (m - M),
            ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have hs : s < m - M := Finset.mem_range.mp hs
        have hz : s + M + 1 - m = 0 := by omega
        rw [hz]
        simp
      have htail :
          (∑ s ∈ Finset.Ico (m - M) m,
            ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) =
            ((m : ℝ) - 2 * M + 1) * M * (M + 1) / 2 +
              2 * (M : ℝ) * (M - 1) * (M + 1) / 3 := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.sub_sub_self (by omega : M ≤ m)]
        have hsum1 (n : ℕ) :
            (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) =
              (n : ℝ) * (n - 1) / 2 + n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one, sum_range_cast_eq]
        have hsumt2 (n : ℕ) :
            (∑ i ∈ Finset.range n, ((i : ℝ) ^ 2 + i)) =
              (n : ℝ) * (n - 1) * (2 * n - 1) / 6 +
                (n : ℝ) * (n - 1) / 2 := by
          rw [Finset.sum_add_distrib, sum_range_cast_sq_eq, sum_range_cast_eq]
        calc
          _ = ∑ i ∈ Finset.range M,
              (((m : ℝ) - 2 * M + 1) * ((i : ℝ) + 1) +
                2 * ((i : ℝ) ^ 2 + i)) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi : i < M := Finset.mem_range.mp hi
            have hfirst : m ≤ 2 * (m - M + i) + 1 := by omega
            have hsecond : m ≤ m - M + i + M + 1 := by omega
            have hsubM : ((m - M : ℕ) : ℝ) = (m : ℝ) - M := by
              rw [Nat.cast_sub (by omega : M ≤ m)]
            rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond]
            push_cast
            rw [hsubM]
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1,
              hsumt2]
            ring
      rw [hprefix, htail, zero_add]
    rw [hcast, Finset.sum_sub_distrib, hamb, hcorr]
    have hcoef : ((m - 2 * M + 1 : ℕ) : ℝ) =
        (m : ℝ) - 2 * (M : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hMle]
      push_cast
      ring
    rw [hcoef]
    ring
  simpa [roundedRankPolynomial, M] using hformula

private theorem roundedSourcePolynomial_div_cube_eq_model {m M L : ℕ} (hm : 0 < m)
    (hML : M ≤ L) :
    roundedSourcePolynomial m M L / (m : ℝ) ^ 3 =
      roundedSourceModel (((M : ℝ) / m, (L : ℝ) / m), (m : ℝ)⁻¹) := by
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hsub : ((L - M : ℕ) : ℝ) = (L : ℝ) - M := by
    rw [Nat.cast_sub hML]
  unfold roundedSourcePolynomial roundedSourceModel
  rw [hsub]
  field_simp

private theorem roundedRankPolynomial_div_cube_eq_model {m M : ℕ} (hm : 0 < m)
    (hM : 2 * M ≤ m) :
    roundedRankPolynomial m M / (m : ℝ) ^ 3 =
      roundedRankModel ((M : ℝ) / m, (m : ℝ)⁻¹) := by
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hcast : ((m - 2 * M + 1 : ℕ) : ℝ) = (m : ℝ) - 2 * (M : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hM]
    push_cast
    ring
  unfold roundedRankPolynomial roundedRankModel
  rw [hcast]
  field_simp

private theorem roundedSourceNormalized_eq_model {m : ℕ} (hm : 0 < m) :
    firstOrderNormalizedSourceCount (1 / 2) (3 / 4) m =
      roundedSourceModel
        (((⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) / m,
          (⌊(3 / 2 : ℝ) * m⌋₊ : ℝ) / m), (m : ℝ)⁻¹) := by
  unfold firstOrderNormalizedSourceCount
  rw [roundedSourceCount_eq_polynomial hm,
    roundedSourcePolynomial_div_cube_eq_model hm (Nat.floor_mono (by
      have hm0 : (0 : ℝ) ≤ m := by positivity
      nlinarith))]

private theorem roundedRankNormalized_eq_model {m : ℕ} (hm : 0 < m) :
    firstOrderNormalizedRankCount (1 / 2) (3 / 4) m =
      roundedRankModel ((⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) / m, (m : ℝ)⁻¹) := by
  have hMcap : firstOrderRateDerivativeCap (1 / 2) (3 / 4) m = ⌊(1 / 4 : ℝ) * m⌋₊ := by
    norm_num [firstOrderRateDerivativeCap, firstOrderRateBeta]
  unfold firstOrderNormalizedRankCount
  rw [hMcap, roundedRankCount_eq_polynomial hm,
    roundedRankPolynomial_div_cube_eq_model hm (by
      have hM : (⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) ≤ (1 / 4 : ℝ) * m :=
        Nat.floor_le (by positivity)
      exact_mod_cast (by nlinarith [hM] : 2 * (⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) ≤ m))]

private theorem concreteSourceNormalized_tendsto :
    Tendsto (firstOrderNormalizedSourceCount (1 / 2) (3 / 4)) atTop
      (𝓝 (firstOrderSourceDensity (1 / 2) (3 / 4)
        (firstOrderRateBeta (1 / 2) (3 / 4)))) := by
  have hM : Tendsto (fun m : ℕ =>
      (⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (1 / 4 : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (a := (1 / 4 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun m : ℕ =>
      (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (3 / 2 : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (a := (3 / 2 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hpair : Tendsto (fun m : ℕ =>
      ((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m,
        (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m)) atTop
      (𝓝 ((1 / 4 : ℝ), (3 / 2 : ℝ))) := hM.prodMk_nhds hL
  have hargs : Tendsto (fun m : ℕ =>
      (((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m,
        (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m), (m : ℝ)⁻¹)) atTop
      (𝓝 (((1 / 4 : ℝ), (3 / 2 : ℝ)), (0 : ℝ))) := hpair.prodMk_nhds he
  have hcont : ContinuousAt roundedSourceModel (((1 / 4 : ℝ), (3 / 2 : ℝ)), 0) := by
    unfold roundedSourceModel
    fun_prop
  have hmodel : Tendsto (roundedSourceModel ∘ fun m : ℕ =>
      (((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m,
        (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m), (m : ℝ)⁻¹)) atTop
      (𝓝 (91 / 768 : ℝ)) := by
    have h := hcont.tendsto.comp hargs
    have heval : roundedSourceModel (((1 / 4 : ℝ), (3 / 2 : ℝ)), 0) = 91 / 768 := by
      norm_num [roundedSourceModel]
    rw [heval] at h
    exact h
  have hlimit : firstOrderSourceDensity (1 / 2) (3 / 4)
      (firstOrderRateBeta (1 / 2) (3 / 4)) = 91 / 768 := by
    rw [concrete_rate_ratio]
    norm_num [firstOrderSourceDensity]
  rw [hlimit]
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  simp only [Function.comp_apply]
  rw [roundedSourceNormalized_eq_model hm]

private theorem concreteRankNormalized_tendsto :
    Tendsto (firstOrderNormalizedRankCount (1 / 2) (3 / 4)) atTop
      (𝓝 (firstOrderRankDensity (firstOrderRateBeta (1 / 2) (3 / 4)))) := by
  have hM : Tendsto (fun m : ℕ =>
      (⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (1 / 4 : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (a := (1 / 4 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hargs : Tendsto (fun m : ℕ =>
      ((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m, (m : ℝ)⁻¹)) atTop
      (𝓝 ((1 / 4 : ℝ), (0 : ℝ))) := hM.prodMk_nhds he
  have hcont : ContinuousAt roundedRankModel ((1 / 4 : ℝ), (0 : ℝ)) := by
    unfold roundedRankModel
    fun_prop
  have hmodel : Tendsto (roundedRankModel ∘ fun m : ℕ =>
      ((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m, (m : ℝ)⁻¹)) atTop
      (𝓝 (19 / 192 : ℝ)) := by
    have h := hcont.tendsto.comp hargs
    have heval : roundedRankModel ((1 / 4 : ℝ), 0) = 19 / 192 := by
      norm_num [roundedRankModel]
    rw [heval] at h
    exact h
  have hlimit : firstOrderRankDensity (firstOrderRateBeta (1 / 2) (3 / 4)) = 19 / 192 := by
    rw [concrete_rate_ratio]
    norm_num [firstOrderRankDensity]
  rw [hlimit]
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  simp only [Function.comp_apply]
  rw [roundedRankNormalized_eq_model hm]

/-- The concrete normalized limits give a finite certificate through the limit theorem. -/
example : Nonempty (FirstOrderFiniteRateParameters (1 / 2) (3 / 4)) := by
  exact exists_firstOrderFiniteRateParameters_of_tendsto concreteSourceNormalized_tendsto
    concreteRankNormalized_tendsto (by
      rw [concrete_rate_ratio]
      norm_num [firstOrderSourceDensity, firstOrderRankDensity])

/-! ### Finite rate parameters -/

private def concreteFiniteParameters : FirstOrderFiniteRateParameters (1 / 2 : ℝ) (3 / 4 : ℝ) :=
  ⟨4, by norm_num, by norm_num [FirstOrderFiniteRateTest, firstOrderRateDerivativeCap,
    firstOrderRateJetDegree, firstOrderRateBeta, firstOrderSourceCount, firstOrderRankCount,
    Finset.sum_range_succ]⟩

/-- The rational finite test computes the same strict surplus, `17 < 18`. -/
example : FirstOrderRationalFiniteTest (1 / 2 : ℚ) (3 / 4 : ℚ) 4 := by
  norm_num [FirstOrderRationalFiniteTest, firstOrderRationalSourceCount,
    firstOrderRankCount, Finset.sum_range_succ]

/-- At the concrete certificate, the scaled kernel-height estimate is its challenge degree `102`. -/
example : 1 * concreteFiniteParameters.rankCount * concreteFiniteParameters.jetDegree /
      (18 - 1 * concreteFiniteParameters.rankCount) ≤
    concreteFiniteParameters.challengeDegree := by
  have hsurplus := concreteFiniteParameters.sourceCount_gt_rankCount
  have h := scaledKernelHeight_le_floor (n := 1) (N := 18)
    (r := concreteFiniteParameters.rankCount) (mu := concreteFiniteParameters.jetDegree)
    hsurplus (by
      norm_num [FirstOrderFiniteRateParameters.sourceCount, concreteFiniteParameters,
        FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
        firstOrderRateDerivativeCap, firstOrderRateJetDegree, firstOrderRateBeta,
        firstOrderSourceCount, Finset.sum_range_succ])
  change 1 * concreteFiniteParameters.rankCount * concreteFiniteParameters.jetDegree /
      (18 - 1 * concreteFiniteParameters.rankCount) ≤
        max 1 ⌊(concreteFiniteParameters.rankCount : ℝ) * concreteFiniteParameters.jetDegree /
          (concreteFiniteParameters.sourceCount - concreteFiniteParameters.rankCount)⌋₊
  exact h.trans (le_max_right _ _)

/-- At rate `1/2`, agreement `3/4`, block length `4`, the scaled source count is at most `91`. -/
example :
    4 * firstOrderSourceCount (1 / 2) (3 / 4) 4 1 6 ≤
      firstOrderDimensionCount 2 3 4 1 6 := by
  apply firstOrderSourceCount_mul_le_firstOrderDimensionCount <;> norm_num

/-- A positive residual parameter preserves the source-to-rank residual comparison. -/
example : (2 : ℝ) * max (3 * (1 / 2 : ℝ) - (1 / 2) * 1) 0 ≤ max (3 * 2 - 1 * 1) 0 := by
  have h := mul_max_rateResidual_le_max_residual (rate := 1 / 2) (a := 1)
    (n := 2) (D := 1) (A := 2) (m := 3) (t := 1) (by norm_num) (by norm_num)
  norm_num at h ⊢

/-! ### Hybrid constants -/

/-- The fiber stage sum at `D = 2`, `μ = 3`, `e = M = 2` is bounded by `2DT`. -/
example : (regularFiberStageSum 2 3 2 : ℝ) ≤ 2 * 2 * stageStaircase 3 2 :=
  regularFiberStageSum_cast_le (by norm_num) (by norm_num) (by norm_num)

/-- The joint stage sum at `D = 2`, `h = 1`, `μ = 3`, `e = M = 2` is bounded by its charge. -/
example : (regularJointStageSum 2 1 3 2 : ℝ) ≤
    (12 * 2 ^ 2 * 1 + 4 * 2) * stageStaircase 3 2 :=
  by
    have h := regularJointStageSum_cast_le (D := 2) (h := 1) (μ := 3) (M := 2) (e := 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    all_goals exact h

/-- The list charge increases from stage `0` to stage `1` at `θ = D = 1`, `μ = 2`. -/
example : firstOrderListCharge 1 1 2 0 ≤ firstOrderListCharge 1 1 2 1 :=
  firstOrderListCharge_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Both balanced-split coordinate ratios are at most `2θ` for `n = 10`, `D = 1`, `A = 4`. -/
example : retainedCoordinateRatio 10 4 (balancedSplit 1 4) ≤
      2 * agreementIncidenceRatio 10 1 4 ∧
    fixedCoordinateRatio 10 1 (balancedSplit 1 4) ≤ 2 * agreementIncidenceRatio 10 1 4 := by
  exact ⟨retainedCoordinateRatio_balancedSplit_le (by norm_num) (by norm_num),
    fixedCoordinateRatio_balancedSplit_le 10 1 4⟩

/-- The optimized list charge is below its closed constant at `θ = D = 1`, `μ = 2`, `M = 1`. -/
example : maxFirstOrderListCharge 1 1 2 1 ≤ firstOrderListConstant 1 1 2 1 :=
  maxFirstOrderListCharge_le_firstOrderListConstant (by norm_num) (by norm_num) (by norm_num)

/-- The optimized exception charge is below its closed constant for `n = 4`, `D = 1`, `A = 3`. -/
example : maxMinFirstOrderExceptionCharge (agreementIncidenceRatio 4 1 3) 4 1 3 1 2 0 ≤
    firstOrderExceptionConstant (agreementIncidenceRatio 4 1 3) 4 1 1 2 0 :=
  maxMinFirstOrderExceptionCharge_le_firstOrderExceptionConstant (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Concrete list and balanced-split exception charges satisfy their direct closed bounds. -/
example : firstOrderListCharge 1 1 2 1 ≤ firstOrderListConstant 1 1 2 1 ∧
    firstOrderExceptionCharge (agreementIncidenceRatio 4 1 3) 4 1 3 1 2 1
        (balancedSplit 1 3) ≤
      firstOrderExceptionConstant (agreementIncidenceRatio 4 1 3) 4 1 1 2 1 := by
  exact ⟨firstOrderListCharge_le_firstOrderListConstant (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    firstOrderExceptionCharge_balancedSplit_le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)⟩

/-! ### Rate and polynomial envelopes -/

/-- For rate fraction `1/4` and agreement fraction `1/2`, the incidence ratio is at most `4`. -/
example : agreementIncidenceRatio 4 1 2 ≤ 1 / ((1 / 2 : ℝ) - 1 / 4) := by
  exact agreementIncidenceRatio_le_one_div_sub (n := 4) (D := 1) (A := 2)
    (ρ := 1 / 4) (a := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The cubic envelope at `C = θ = 1`, `q = n = μ = 2`, and `D = M = 1`. -/
example : firstOrderListConstant 1 1 2 1 ≤ 48 := by
  have h := firstOrderListConstant_le_cubic (C := 1) (q := 2) (θ := 1) (n := 2) (D := 1)
    (μ := 2) (M := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [stageStaircase])
  norm_num at h ⊢
  exact h

/-- The quintic envelope at `C = θ = 1`, `q = n = μ = 2`, and `D = M = h = 1`. -/
example : firstOrderExceptionConstant 1 2 1 1 2 1 ≤ 5760 := by
  have h := firstOrderExceptionConstant_le_quintic (C := 1) (q := 2) (θ := 1) (n := 2) (D := 1)
    (h := 1) (μ := 2) (M := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [stageStaircase])
  norm_num at h ⊢
  exact h

/-! ### Curve charges -/

/-- Increasing total degree or derivative degree increases the concrete stage charges. -/
example : orderZeroCurveStageCharge 1 1 1 1 1 1 ≤ orderZeroCurveStageCharge 1 1 1 1 2 1 ∧
    orderOneCurveStageCharge 3 1 1 1 1 1 1 1 1 1 ≤
      orderOneCurveStageCharge 3 1 1 1 1 1 2 1 1 1 ∧
    orderOneCurveStageCharge 3 1 1 1 1 1 2 0 1 1 ≤
      orderOneCurveStageCharge 3 1 1 1 1 1 2 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (orderZeroCurveStageCharge_mono 1 1 (s := 1) (c := 1)
      (by norm_num) (by norm_num) 1) (by norm_num)
  · exact (orderOneCurveStageCharge_mono_total 3 1 1 (s := 1) (η := 1) (t := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1) (by norm_num)
  · exact orderOneCurveStageCharge_mono_derivative 3 1 1 (s := 1) (η := 1) (t := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num)

/-- The order-one fiber degree is bounded by `j` times the total Taylor cap. -/
example : 2 ≤ firstOrderCurveFiberStageOne 3 2 1 2 ∧
    firstOrderCurveFiberStageOne 3 3 1 2 ≤ 3 * firstOrderTaylorTotalCap 3 2 := by
  exact ⟨le_firstOrderCurveFiberStageOne (by norm_num),
    firstOrderCurveFiberStageOne_le_mul_totalCap (by norm_num)⟩

/-- The fiber and joint stage degrees are monotone in total jet degree for concrete parameters. -/
example : firstOrderCurveFiberStageOne 3 2 1 2 ≤ firstOrderCurveFiberStageOne 3 3 1 2 ∧
    firstOrderCurveJointStageOne 3 1 1 2 1 2 ≤ firstOrderCurveJointStageOne 3 1 1 3 1 2 := by
  exact ⟨firstOrderCurveFiberStageOne_mono_total (by norm_num),
    firstOrderCurveJointStageOne_mono_total (by norm_num)⟩

/-- The fiber and joint stage degrees are monotone in derivative degree at concrete parameters. -/
example : firstOrderCurveFiberStageOne 3 3 1 2 ≤ firstOrderCurveFiberStageOne 3 3 2 2 ∧
    firstOrderCurveJointStageOne 3 1 1 3 1 2 ≤ firstOrderCurveJointStageOne 3 1 1 3 2 2 := by
  exact ⟨firstOrderCurveFiberStageOne_mono_derivative (by norm_num) (by norm_num),
    firstOrderCurveJointStageOne_mono_derivative (by norm_num) (by norm_num)⟩

/-- The curve bound is monotone when the direct incidence factor rises from `1` to `2`. -/
example : firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 1 ≤
    firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 2 :=
  firstOrderCurveBound_mono_directFactor 8 3 2 3 4 3 1 1 1 2 (by norm_num)

/-- At `K = 3`, the order-zero charge is below the order-one charge at `v = 3`. -/
example : orderZeroCurveStageCharge 1 1 1 1 3 2 ≤
    orderOneCurveStageCharge 3 1 1 1 1 1 3 1 2 1 :=
  orderZeroCurveStageCharge_le_orderOne 3 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 3 2

end ReedSolomon.HiddenDerivative
