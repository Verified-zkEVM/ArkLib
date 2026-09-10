/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateRounding

/-!
# Asymptotics of the rounded first-order counts

This file proves the two normalized finite-sum estimates that make the multiplicity search in
`RateRounding` terminate.  The rank proof uses the signed cubic upper count, which applies on
both branches of the exact local-rank formula.
-/

@[expose] public section

open scoped BigOperators Topology

namespace ReedSolomon.HiddenDerivative

noncomputable section

private def linearSumModel (x : ℝ) : ℝ := x * (x - 1) / 2

private def squareSumModel (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem sum_range_cast_eq_linearSumModel (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = linearSumModel n := by
  induction n with
  | zero => simp [linearSumModel]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [linearSumModel]
      push_cast
      ring

private theorem sum_range_sq_cast_eq_squareSumModel (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = squareSumModel n := by
  induction n with
  | zero => simp [squareSumModel]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [squareSumModel]
      push_cast
      ring

private def rankCubicNormalizedModel (u v : ℝ) : ℝ :=
  (u + v) * ((1 - v) / 2 + v) -
    (2 * ((1 - v) * (2 - v) / 6 -
        (1 - u) * (1 - u - v) * (2 * (1 - u) - v) / 6) +
      (2 * u + 3 * v - 3) *
        ((1 - v) / 2 - (1 - u) * (1 - u - v) / 2) +
      u * (v - 1) * (u + v - 1))

private theorem rankCubicNormalizedModel_zero (u : ℝ) :
    rankCubicNormalizedModel u 0 = firstOrderRankCubicEnvelope u := by
  rw [rankCubicNormalizedModel, firstOrderRankCubicEnvelope]
  ring

private theorem cubicUpperCount_normalized_eq_model {m M : ℕ}
    (hm : 0 < m) (hM : M ≤ m) :
    firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 =
      rankCubicNormalizedModel ((M : ℝ) / m) ((m : ℝ)⁻¹) := by
  have hamb (n : ℕ) :
      (∑ x ∈ Finset.range n, ((x + 1 : ℕ) : ℝ) * (M + 1)) =
        (M + 1) * (linearSumModel n + n) := by
    calc
      _ = (M + 1 : ℝ) * ((∑ x ∈ Finset.range n, (x : ℝ)) + n) := by
        push_cast
        ring_nf
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [sum_range_cast_eq_linearSumModel]
  have hcorrection (n : ℕ) :
      (∑ x ∈ Finset.range n,
        (((2 * x + 1 : ℕ) : ℝ) - m) * (((x + M + 1 : ℕ) : ℝ) - m)) =
        2 * squareSumModel n + (2 * M + 3 - 3 * m) * linearSumModel n +
          n * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ x ∈ Finset.range n,
          (2 * (x : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * x +
            (1 - m) * (M + 1 - m)) := by
        apply Finset.sum_congr rfl
        intro x _
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, sum_range_cast_eq_linearSumModel,
          sum_range_sq_cast_eq_squareSumModel]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [firstOrderRankCubicUpperCount,
    Finset.sum_Ico_eq_sub _ (Nat.sub_le m M), hamb, hcorrection, hcorrection]
  rw [Nat.cast_sub hM]
  simp only [linearSumModel, squareSumModel, rankCubicNormalizedModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

/-- The signed cubic upper count converges to the cubic rank envelope. -/
theorem tendsto_firstOrderRankCubicUpperCount {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    Filter.Tendsto
      (fun m : ℕ ↦ firstOrderRankCubicUpperCount m (Nat.floor (beta * m)) /
        (m : ℝ) ^ 3)
      Filter.atTop (nhds (firstOrderRankCubicEnvelope beta)) := by
  have hcap : Filter.Tendsto (fun m : ℕ ↦ ((Nat.floor (beta * m) : ℕ) : ℝ) / m)
      Filter.atTop (nhds beta) := by
    simpa [Function.comp_def] using (tendsto_nat_floor_mul_div_atTop hbeta0).comp
      tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun m : ℕ ↦ ((m : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmodel : Filter.Tendsto
      (fun m : ℕ ↦ rankCubicNormalizedModel
        (((Nat.floor (beta * m) : ℕ) : ℝ) / m) ((m : ℝ)⁻¹))
      Filter.atTop (nhds (rankCubicNormalizedModel beta 0)) := by
    have hcontinuous : Continuous
        (fun p : ℝ × ℝ ↦ rankCubicNormalizedModel p.1 p.2) := by
      simp only [rankCubicNormalizedModel]
      fun_prop
    exact Filter.Tendsto.comp hcontinuous.continuousAt (hcap.prodMk_nhds hinv)
  rw [rankCubicNormalizedModel_zero] at hmodel
  apply hmodel.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  symm
  apply cubicUpperCount_normalized_eq_model hm
  have hreal : ((Nat.floor (beta * m) : ℕ) : ℝ) ≤ (m : ℝ) := calc
    ((Nat.floor (beta * m) : ℕ) : ℝ) ≤ beta * m :=
      Nat.floor_le (mul_nonneg hbeta0 (Nat.cast_nonneg m))
    _ ≤ m := by
      simpa using mul_le_mul_of_nonneg_right hbeta1 (Nat.cast_nonneg m)
  exact_mod_cast hreal

/-- A convenient lower sum obtained by dropping the harmless `+1` in the source multiplicity
and stopping at `floor (m*a/R)`. -/
def firstOrderSourceLowerCount (R a : ℝ) (m M L : ℕ) : ℝ :=
  ∑ t ∈ Finset.range L, (min t M : ℕ) * (m * a - R * t)

/-- The truncated lower sum is bounded by the actual rounded source count. -/
theorem firstOrderSourceLowerCount_le_rateSourceCount {R a : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (m M : ℕ) :
    firstOrderSourceLowerCount R a m M (Nat.floor (m * a / R)) ≤
      firstOrderRateSourceCount R a m M (Nat.ceil (m * a / R)) := by
  let L := Nat.floor (m * a / R)
  let mu := Nat.ceil (m * a / R)
  have hx : 0 ≤ (m : ℝ) * a / R := div_nonneg (mul_nonneg (Nat.cast_nonneg m) ha) hR.le
  have hLmu : L ≤ mu := by
    have hreal : (L : ℝ) ≤ mu := (Nat.floor_le hx).trans (Nat.le_ceil _)
    exact_mod_cast hreal
  calc
    firstOrderSourceLowerCount R a m M L ≤
        ∑ t ∈ Finset.range L,
          ((min t M + 1 : ℕ) : ℝ) * max (m * a - R * t) 0 := by
      rw [firstOrderSourceLowerCount]
      apply Finset.sum_le_sum
      intro t ht
      have htL : t ≤ L := (Finset.mem_range.mp ht).le
      have htReal : (t : ℝ) ≤ (m : ℝ) * a / R :=
        (Nat.cast_le.mpr htL).trans (Nat.floor_le hx)
      have hres : 0 ≤ (m : ℝ) * a - R * t := by
        have := mul_le_mul_of_nonneg_left htReal hR.le
        field_simp [ne_of_gt hR] at this ⊢
        nlinarith
      rw [max_eq_left hres]
      apply mul_le_mul_of_nonneg_right _ hres
      norm_cast
      omega
    _ ≤ ∑ t ∈ Finset.range (mu + 1),
          ((min t M + 1 : ℕ) : ℝ) * max (m * a - R * t) 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp ht
        omega
      · intro t _ _
        positivity
    _ = firstOrderRateSourceCount R a m M mu := by
      rw [firstOrderRateSourceCount]

private def sourceLowerNormalizedModel (R a u c v : ℝ) : ℝ :=
  a * u * (u - v) / 2 - R * u * (u - v) * (2 * u - v) / 6 +
    u * (a * (c - u) - R * (c * (c - v) - u * (u - v)) / 2)

private theorem sourceLowerNormalizedModel_zero {R a beta : ℝ} (hR : R ≠ 0) :
    sourceLowerNormalizedModel R a beta (a / R) 0 =
      firstOrderSourceDensity R a beta := by
  rw [sourceLowerNormalizedModel, firstOrderSourceDensity]
  field_simp
  ring

private theorem sourceLowerCount_normalized_eq_model {R a : ℝ} {m M L : ℕ}
    (hm : 0 < m) (hML : M ≤ L) :
    firstOrderSourceLowerCount R a m M L / (m : ℝ) ^ 3 =
      sourceLowerNormalizedModel R a ((M : ℝ) / m) ((L : ℝ) / m) ((m : ℝ)⁻¹) := by
  have hsplit :
      firstOrderSourceLowerCount R a m M L =
        a * m * linearSumModel M - R * squareSumModel M +
          M * (a * m * (L - M) -
            R * (linearSumModel L - linearSumModel M)) := by
    rw [firstOrderSourceLowerCount, ← Finset.sum_range_add_sum_Ico _ hML]
    have hfirst :
        (∑ t ∈ Finset.range M, (min t M : ℕ) * (m * a - R * t)) =
          a * m * linearSumModel M - R * squareSumModel M := by
      calc
        _ = ∑ t ∈ Finset.range M, ((t : ℝ) * (m * a - R * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_left (Finset.mem_range.mp ht).le]
        _ = ∑ t ∈ Finset.range M,
            (a * m * (t : ℝ) - R * (t : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_range_cast_eq_linearSumModel, sum_range_sq_cast_eq_squareSumModel]
    have htail :
        (∑ t ∈ Finset.Ico M L, (min t M : ℕ) * (m * a - R * t)) =
          M * (a * m * (L - M) -
            R * (linearSumModel L - linearSumModel M)) := by
      calc
        _ = ∑ t ∈ Finset.Ico M L, ((M : ℝ) * (m * a - R * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_right (Finset.mem_Ico.mp ht).1]
        _ = _ := by
          have hsum (n : ℕ) :
              (∑ t ∈ Finset.range n, ((m : ℝ) * a - R * t)) =
                n * (m * a) - R * linearSumModel n := by
            induction n with
            | zero => simp [linearSumModel]
            | succ n ih =>
                rw [Finset.sum_range_succ, ih]
                simp only [linearSumModel]
                push_cast
                ring
          rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hML, hsum, hsum]
          ring
    exact congrArg₂ (· + ·) hfirst htail
  rw [hsplit]
  simp only [linearSumModel, squareSumModel, sourceLowerNormalizedModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]

/-- The normalized source lower sum has the limiting first-order source density. -/
theorem tendsto_firstOrderSourceLowerCount {R a beta : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hbeta0 : 0 ≤ beta) (hbeta : beta < a / R) :
    Filter.Tendsto
      (fun m : ℕ ↦ firstOrderSourceLowerCount R a m (Nat.floor (beta * m))
        (Nat.floor ((a / R) * m)) / (m : ℝ) ^ 3)
      Filter.atTop (nhds (firstOrderSourceDensity R a beta)) := by
  have hcap : Filter.Tendsto (fun m : ℕ ↦ ((Nat.floor (beta * m) : ℕ) : ℝ) / m)
      Filter.atTop (nhds beta) := by
    simpa [Function.comp_def] using (tendsto_nat_floor_mul_div_atTop hbeta0).comp
      tendsto_natCast_atTop_atTop
  have hcutoff : Filter.Tendsto
      (fun m : ℕ ↦ ((Nat.floor ((a / R) * m) : ℕ) : ℝ) / m)
      Filter.atTop (nhds (a / R)) := by
    simpa [Function.comp_def] using
      (tendsto_nat_floor_mul_div_atTop (div_nonneg ha hR.le)).comp
        tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun m : ℕ ↦ ((m : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmodel : Filter.Tendsto
      (fun m : ℕ ↦ sourceLowerNormalizedModel R a
        (((Nat.floor (beta * m) : ℕ) : ℝ) / m)
        (((Nat.floor ((a / R) * m) : ℕ) : ℝ) / m) ((m : ℝ)⁻¹))
      Filter.atTop (nhds (sourceLowerNormalizedModel R a beta (a / R) 0)) := by
    have hcontinuous : Continuous
        (fun p : ℝ × ℝ × ℝ ↦ sourceLowerNormalizedModel R a p.1 p.2.1 p.2.2) := by
      simp only [sourceLowerNormalizedModel]
      fun_prop
    exact Filter.Tendsto.comp hcontinuous.continuousAt
      (hcap.prodMk_nhds (hcutoff.prodMk_nhds hinv))
  rw [sourceLowerNormalizedModel_zero (ne_of_gt hR)] at hmodel
  apply hmodel.congr'
  have hevent : ∀ᶠ m : ℕ in Filter.atTop,
      Nat.floor (beta * m) ≤ Nat.floor ((a / R) * m) := by
    filter_upwards with m
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hbeta.le (Nat.cast_nonneg m))
  filter_upwards [Filter.eventually_ge_atTop 1, hevent] with m hm hML
  symm
  exact sourceLowerCount_normalized_eq_model hm hML

/-- Above the clean first-order threshold, the rounded multiplicity search terminates. -/
theorem exists_firstOrderFiniteRateParameters {R a : ℝ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1)
    (hthreshold : firstOrderRateThreshold R < a) :
    Nonempty (FirstOrderFiniteRateParameters R a) := by
  let beta := firstOrderRateBeta R a
  have hRone : R < 1 := hRa.trans haone
  have hbeta0 : 0 < beta := firstOrderRateBeta_pos haone hRone
  have hbeta1 : beta < 1 :=
    (firstOrderRateBeta_lt_three_four hR hRa haone).trans (by norm_num)
  have hbetaCutoff : beta < a / R :=
    firstOrderRateBeta_lt_agreement_div_rate hR hRa haone
  have hlimitGap : firstOrderRankCubicEnvelope beta <
      firstOrderSourceDensity R a beta := by
    have hclean := firstOrderCleanExpression_gt_one hR hRone hthreshold
    have hbracket := firstOrderRateBeta_bracket R a (ne_of_gt hR) (by linarith)
    have hfactor := firstOrderSourceDensity_sub_cubicEnvelope R a beta (ne_of_gt hR)
    dsimp only [beta] at hbracket hfactor ⊢
    have hbetaPos := firstOrderRateBeta_pos haone hRone
    nlinarith
  have hrankLimit := tendsto_firstOrderRankCubicUpperCount hbeta0.le hbeta1.le
  have hsourceLimit := tendsto_firstOrderSourceLowerCount hR
    (hR.le.trans hRa.le) hbeta0.le hbetaCutoff
  have heventually : ∀ᶠ m : ℕ in Filter.atTop,
      firstOrderRankCubicUpperCount m (Nat.floor (beta * m)) / (m : ℝ) ^ 3 <
        firstOrderSourceLowerCount R a m (Nat.floor (beta * m))
          (Nat.floor ((a / R) * m)) / (m : ℝ) ^ 3 :=
    Filter.Tendsto.eventually_lt hrankLimit hsourceLimit hlimitGap
  obtain ⟨m, hgap, hm⟩ :=
    (heventually.and (Filter.eventually_ge_atTop 1)).exists
  let M := Nat.floor (beta * m)
  let mu := Nat.ceil (m * a / R)
  have hscale : (0 : ℝ) < (m : ℝ) ^ 3 := pow_pos (Nat.cast_pos.mpr hm) _
  have hrankUpper : firstOrderNormalizedRankCount R a m ≤
      firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 := by
    rw [firstOrderNormalizedRankCount]
    apply div_le_div_of_nonneg_right _ hscale.le
    simpa [M, beta, firstOrderRateDerivativeCap] using
      firstOrderRateRankCount_le_cubicUpperCount m M
  have hsourceLower :
      firstOrderSourceLowerCount R a m M (Nat.floor ((a / R) * m)) / (m : ℝ) ^ 3 ≤
        firstOrderNormalizedSourceCount R a m := by
    rw [firstOrderNormalizedSourceCount]
    apply div_le_div_of_nonneg_right _ hscale.le
    have hlower := firstOrderSourceLowerCount_le_rateSourceCount hR
      (hR.le.trans hRa.le) m M
    rw [show (a / R) * (m : ℝ) = (m : ℝ) * a / R by ring]
    simpa only [M, beta, firstOrderRateDerivativeCap, firstOrderRateJetDegree,
      mul_div_assoc, mul_comm a] using hlower
  have hnormalized : firstOrderNormalizedRankCount R a m <
      firstOrderNormalizedSourceCount R a m := by
    exact hrankUpper.trans_lt (hgap.trans_le hsourceLower)
  refine ⟨⟨m, hm, ?_⟩⟩
  rw [firstOrderNormalizedRankCount, firstOrderNormalizedSourceCount] at hnormalized
  exact (div_lt_div_iff_of_pos_right hscale).mp hnormalized

end

end ReedSolomon.HiddenDerivative
