/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.Uniform
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
/-!
# Uniform first-order parameters for mutual correlated agreement

This module gives an explicit shifted-height certificate and numerical bounds for the
first-order charges at support `(12, 4, 23)` and challenge height `276`. It also provides a
retention split whose coordinate ratios are controlled by the agreement-incidence ratio.

## Main statements

* `uniformFirstOrderMCA_parameters`: the support has the positive degree budgets and strict
  shifted-slot surplus needed by the curve constructor.
* `uniformFirstOrderMCASplit` and `uniformFirstOrderMCASplit_bounds`: the admissible retained
  split `D + ⌈(A - D) / 42⌉`.
* `uniformFirstOrderMCASplit_retainedCoordinateRatio_le` and
  `uniformFirstOrderMCASplit_fixedCoordinateRatio_le`: bounds for the two ratios at the split.
* `uniformFirstOrderMCA_agreementIncidenceRatio_le` and
  `uniformFirstOrderMCA_degree_mul_agreementIncidenceRatio_le`: bounds in the gap-`6/25` regime.
* `uniformFirstOrderMCA_regularFiberStageSum_four` and
  `uniformFirstOrderMCA_regularJointStageSum_four`: exact formulas for the four regular stages.
* `uniformFirstOrderMCA_exceptionCharge_le` and
  `uniformFirstOrderMCA_exceptionCharge_le_ceiling`: explicit bounds for the exception charge.
* `uniformFirstOrderMCA_optimizedExceptionCharge_le_ceiling`: the optimized exception charge
  satisfies the same integral ceiling.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

set_option maxRecDepth 4096

/-- Height weight of the first `q` total-degree shells. -/
private def uniformFirstOrderMCAHeightWeightUpTo (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q, (min t 4 + 1) * (277 - t)

/-- Total-degree height weight of the first `q` shells. -/
private def uniformFirstOrderMCAHeightDegreeWeightUpTo (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q, (min t 4 + 1) * t * (277 - t)

/-- First-jet height weight of the first `q` shells. -/
private def uniformFirstOrderMCAHeightFirstJetWeightUpTo (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q,
    ∑ b ∈ Finset.range (min t 4 + 1), b * (277 - t)

private theorem uniformFirstOrderMCAHeightWeightUpTo_eq_nested (q : ℕ) :
    uniformFirstOrderMCAHeightWeightUpTo q =
      ∑ t ∈ Finset.range q,
        Finset.sum (Finset.range (min t 4 + 1)) (fun _ ↦ 277 - t) := by
  simp [uniformFirstOrderMCAHeightWeightUpTo, Finset.sum_const]

private theorem uniformFirstOrderMCAHeightDegreeWeightUpTo_eq_nested (q : ℕ) :
    uniformFirstOrderMCAHeightDegreeWeightUpTo q =
      ∑ t ∈ Finset.range q,
        Finset.sum (Finset.range (min t 4 + 1)) (fun _ ↦ t * (277 - t)) := by
  simp [uniformFirstOrderMCAHeightDegreeWeightUpTo, Finset.sum_const, Nat.mul_assoc]

/-- Prefix accounting for the shifted coefficient-height sum. -/
private theorem uniformFirstOrderMCA_shiftedHeightSlot_accounting_general
    (D A q : ℕ) :
    12 * A * uniformFirstOrderMCAHeightWeightUpTo q +
        uniformFirstOrderMCAHeightFirstJetWeightUpTo q ≤
      (∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
        (12 * A + b - D * t) * (277 - t)) +
        D * uniformFirstOrderMCAHeightDegreeWeightUpTo q := by
  have hleft :
      12 * A * uniformFirstOrderMCAHeightWeightUpTo q +
          uniformFirstOrderMCAHeightFirstJetWeightUpTo q =
        ∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
          (12 * A + b) * (277 - t) := by
    rw [uniformFirstOrderMCAHeightWeightUpTo_eq_nested]
    simp only [uniformFirstOrderMCAHeightFirstJetWeightUpTo, Nat.add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hright :
      (∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
          (12 * A + b - D * t) * (277 - t)) +
          D * uniformFirstOrderMCAHeightDegreeWeightUpTo q =
        ∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
          ((12 * A + b - D * t) * (277 - t) + D * t * (277 - t)) := by
    rw [uniformFirstOrderMCAHeightDegreeWeightUpTo_eq_nested]
    simp only [Nat.mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro b hb
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem uniformFirstOrderMCA_shiftedHeightSlot_accounting
    (D A q heightWeight degreeWeight firstJetWeight : ℕ)
    (hweight : uniformFirstOrderMCAHeightWeightUpTo q = heightWeight)
    (hdegree : uniformFirstOrderMCAHeightDegreeWeightUpTo q = degreeWeight)
    (hfirstJet : uniformFirstOrderMCAHeightFirstJetWeightUpTo q = firstJetWeight) :
    12 * A * heightWeight + firstJetWeight ≤
      (∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
        (12 * A + b - D * t) * (277 - t)) + D * degreeWeight := by
  have haccounting := uniformFirstOrderMCA_shiftedHeightSlot_accounting_general D A q
  rw [hweight, hdegree, hfirstJet] at haccounting
  exact haccounting

set_option maxHeartbeats 10000000 in
-- The nine exact interval branches require more than the default heartbeat budget.
/-- The support `(12, 4, 23)` has a strict shifted-slot surplus at height
`276` throughout the gap-`6/25` regime. -/
theorem uniformFirstOrderMCA_heightSlotCount (n k A : ℕ)
    (hk : 2 ≤ k) (hgap : 25 * k + 6 * n ≤ 25 * A) :
    let D := k - 1
    firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 <
      firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
  dsimp only
  let D := k - 1
  have hrow := firstOrderCurveShiftedRowSlotBound_le_of_rankBound
    D A 12 4 23 n 1 276 uniformFirstOrderGradedRankProfile
      (firstOrderGradedRankBound_le_uniformFirstOrderProfile D A)
  have hrow' :
      firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 ≤ n * 81530 := by
    calc
      _ ≤ ∑ t ∈ Finset.range (23 + 1),
          n * uniformFirstOrderGradedRankProfile t * (276 + 1 - t) := hrow
      _ = n * 81530 := by
        norm_num [Finset.sum_range_succ, uniformFirstOrderGradedRankProfile]
        ring
  let slotTerm := fun t ↦
    ∑ b ∈ Finset.range (min t 4 + 1),
      (12 * A + b - D * t) * (276 + 1 - t)
  have hpartial (q : ℕ) (hq : q ≤ 24) :
      (∑ t ∈ Finset.range q, slotTerm t) ≤
        firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
    unfold firstOrderCurveShiftedHeightSlotCount
    simpa only [slotTerm, Nat.one_mul, show 23 + 1 = 24 by norm_num] using
      (Finset.sum_le_sum_of_subset
        (Finset.range_mono hq) :
          (∑ t ∈ Finset.range q, slotTerm t) ≤
            ∑ t ∈ Finset.range 24, slotTerm t)
  apply hrow'.trans_lt
  by_cases h11 : 275 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 24 le_rfl)
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 24
      29100 357890 55445 (by decide) (by decide) (by decide)
    omega
  by_cases h10 : 250 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 23 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 23
      27830 328680 52905 (by decide) (by decide) (by decide)
    omega
  by_cases h9 : 225 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 22 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 22
      26555 300630 50355 (by decide) (by decide) (by decide)
    omega
  by_cases h8 : 200 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 21 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 21
      25275 273750 47795 (by decide) (by decide) (by decide)
    omega
  by_cases h7 : 175 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 20 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 20
      23990 248050 45225 (by decide) (by decide) (by decide)
    omega
  by_cases h6 : 150 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 19 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 19
      22700 223540 42645 (by decide) (by decide) (by decide)
    omega
  by_cases h5 : 125 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 18 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 18
      21405 200230 40055 (by decide) (by decide) (by decide)
    omega
  by_cases h4 : 100 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 17 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 17
      20105 178130 37455 (by decide) (by decide) (by decide)
    omega
  · apply lt_of_lt_of_le ?_ (hpartial 16 (by omega))
    dsimp only [slotTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 16
      18800 157250 34845 (by decide) (by decide) (by decide)
    omega

/-- The height-276 support supplies precisely the ambient-degree, positive-budget,
message-degree, and shifted-slot hypotheses used by the semantic curve constructor. -/
theorem uniformFirstOrderMCA_parameters (n k A : ℕ)
    (hk : 2 ≤ k) (hgap : 25 * k + 6 * n ≤ 25 * A) :
    let D := k - 1
    0 < D ∧ 0 < 12 * A ∧ k ≤ D + 1 ∧
      firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 <
        firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_⟩
  exact uniformFirstOrderMCA_heightSlotCount n k A hk hgap

/-! ## Exact regular-stage arithmetic -/

set_option maxHeartbeats 2000000 in
-- Expanding the four exact cap-sensitive stages needs more than the default budget.
/-- Exact generic-fiber degree of the four regular stages at the identity-pair endpoint. -/
theorem uniformFirstOrderMCA_regularFiberStageSum_four_one : regularFiberStageSum 1 23 4 = 86 := by
  norm_num [regularFiberStageSum, Finset.sum_range_succ, regularTaylorExponent,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap, MvPolynomial.cappedDegreeMixedVolume]

/-- Exact generic-fiber degree of the four regular stages for `D ≥ 2`. -/
theorem uniformFirstOrderMCA_regularFiberStageSum_four (D : ℕ) (hD : 2 ≤ D) :
    regularFiberStageSum D 23 4 = 724 * (D - 2) + 486 := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 2 := ⟨D - 2, by omega⟩
  norm_num [regularFiberStageSum, Finset.sum_range_succ, regularTaylorExponent,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap,
    MvPolynomial.cappedDegreeMixedVolume]
  omega

/-- Exact joint-family degree at the identity-pair endpoint. -/
theorem uniformFirstOrderMCA_regularJointStageSum_four_one :
    regularJointStageSum 1 276 23 4 = 1276 := by
  norm_num [regularJointStageSum, Finset.sum_range_succ,
    firstOrderCurveJointStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap, firstOrderCurveFiberStageOne,
    regularTaylorExponent, MvPolynomial.cappedBidegreeMixedVolume,
    MvPolynomial.cappedDegreeMixedVolume]

/-- Exact joint-family degree of the four regular stages for `D ≥ 2`. -/
theorem uniformFirstOrderMCA_regularJointStageSum_four (D : ℕ) (hD : 2 ≤ D) :
    regularJointStageSum D 276 23 4 =
      1149264 * (D - 2) ^ 2 + 1418984 * (D - 2) + 423252 := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 2 := ⟨D - 2, by omega⟩
  norm_num [regularJointStageSum, Finset.sum_range_succ,
    firstOrderCurveJointStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap, firstOrderCurveFiberStageOne,
    regularTaylorExponent, MvPolynomial.cappedBidegreeMixedVolume,
    MvPolynomial.cappedDegreeMixedVolume]
  have hτ : 2 * (d + 2) - 3 = 2 * d + 1 := by omega
  simp only [hτ]
  have hm1 : d + 2 ≤ 1 + (2 * d + 1) * 19 := by omega
  have hm2 : 2 * d + 1 + (d + 2) ≤ 1 + (2 * d + 1) * 20 := by omega
  have hm3 : (2 * d + 1) * 2 + (d + 2) ≤ 1 + (2 * d + 1) * 21 := by omega
  have hm4 : (2 * d + 1) * 3 + (d + 2) ≤ 1 + (2 * d + 1) * 22 := by omega
  simp only [min_eq_right hm1, min_eq_right hm2, min_eq_right hm3,
    min_eq_right hm4]
  have hs1 : 1 + (2 * d + 1) * 19 - (d + 2) = 18 + 37 * d := by omega
  have hs2 : 1 + (2 * d + 1) * 20 - (2 * d + 1 + (d + 2)) =
      18 + 37 * d := by omega
  have hs3 : 1 + (2 * d + 1) * 21 - ((2 * d + 1) * 2 + (d + 2)) =
      18 + 37 * d := by omega
  have hs4 : 1 + (2 * d + 1) * 22 - ((2 * d + 1) * 3 + (d + 2)) =
      18 + 37 * d := by omega
  simp only [hs1, hs2, hs3, hs4]
  have hsq {c t : ℕ} (hct : c ≤ t) : c ^ 2 ≤ 2 * t * c := by
    rw [pow_two]
    calc
      c * c ≤ t * c := Nat.mul_le_mul_right c hct
      _ ≤ (2 * t) * c := Nat.mul_le_mul_right c (by omega)
      _ = 2 * t * c := by ring
  have hle1 : (d + 2) ^ 2 ≤ 2 * (1 + (2 * d + 1) * 19) * (d + 2) := hsq hm1
  have hle2 : (2 * d + 1 + (d + 2)) ^ 2 ≤
      2 * (1 + (2 * d + 1) * 20) * (2 * d + 1 + (d + 2)) := hsq hm2
  have hle3 : ((2 * d + 1) * 2 + (d + 2)) ^ 2 ≤
      2 * (1 + (2 * d + 1) * 21) * ((2 * d + 1) * 2 + (d + 2)) := hsq hm3
  have hle4 : ((2 * d + 1) * 3 + (d + 2)) ^ 2 ≤
      2 * (1 + (2 * d + 1) * 22) * ((2 * d + 1) * 3 + (d + 2)) := hsq hm4
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hle1, Nat.cast_sub hle2, Nat.cast_sub hle3,
    Nat.cast_sub hle4]
  ring

/-! ## The one-forty-second retention split -/

/-- The retained-stage split `D + ceil((A-D)/42)`. -/
def uniformFirstOrderMCASplit (D A : ℕ) : ℕ :=
  D + (A - D + 41) / 42

private theorem uniformFirstOrderMCASplit_offset_bounds {D A : ℕ} (hDA : D < A) :
    let d := A - D
    let r := (d + 41) / 42
    1 ≤ r ∧ r ≤ d ∧ d ≤ 42 * r ∧ 42 * (r - 1) < d := by
  dsimp only
  omega

/-- The retained-stage split is admissible. -/
theorem uniformFirstOrderMCASplit_bounds {D A : ℕ} (hDA : D < A) :
    D < uniformFirstOrderMCASplit D A ∧ uniformFirstOrderMCASplit D A ≤ A := by
  unfold uniformFirstOrderMCASplit
  obtain ⟨hr, hrd, _, _⟩ := uniformFirstOrderMCASplit_offset_bounds hDA
  omega

/-- At the one-forty-second split, the retained joint ratio costs at most
`42/41` times the direct agreement ratio. -/
theorem uniformFirstOrderMCASplit_retainedCoordinateRatio_le {n D A : ℕ}
    (hDA : D < A) (hAn : A ≤ n) :
    retainedCoordinateRatio n A (uniformFirstOrderMCASplit D A) ≤
      (42 / 41 : ℝ) * agreementIncidenceRatio n D A := by
  let d := A - D
  let N := n - D
  let r := (d + 41) / 42
  obtain ⟨hr, hrd, hdr, hrlt⟩ := uniformFirstOrderMCASplit_offset_bounds hDA
  have hd : 1 ≤ d := by dsimp only [d]; omega
  have hdN : d ≤ N := by dsimp only [d, N]; omega
  have hL : uniformFirstOrderMCASplit D A = D + r := by
    simp only [uniformFirstOrderMCASplit, r, d]
  have hnum : n - uniformFirstOrderMCASplit D A + 1 ≤ N - r + 1 := by
    rw [hL]
    dsimp only [N]
    omega
  have hden : A - uniformFirstOrderMCASplit D A + 1 = d - r + 1 := by
    rw [hL]
    dsimp only [d]
    omega
  have hcross :
      41 * (n - uniformFirstOrderMCASplit D A + 1) * d ≤
        42 * N * (d - r + 1) := by
    calc
      41 * (n - uniformFirstOrderMCASplit D A + 1) * d ≤
          41 * (N - r + 1) * d := by gcongr
      _ ≤ 42 * N * (d - r + 1) := by
        have hrN : r ≤ N := hrd.trans hdN
        have hceil : 42 * r ≤ d + 42 := by omega
        have hdiff : (0 : ℝ) ≤ d + 42 - 42 * r := by
          apply sub_nonneg.mpr
          exact_mod_cast hceil
        have hrOne : (0 : ℝ) ≤ r - 1 := by
          apply sub_nonneg.mpr
          exact_mod_cast hr
        have hfirst : (0 : ℝ) ≤ N * (d + 42 - 42 * r) :=
          mul_nonneg (by positivity) hdiff
        have hsecond : (0 : ℝ) ≤ 41 * d * (r - 1) :=
          mul_nonneg (by positivity) hrOne
        have hreal : ((41 * (N - r + 1) * d : ℕ) : ℝ) ≤
            ((42 * N * (d - r + 1) : ℕ) : ℝ) := by
          push_cast
          rw [Nat.cast_sub hrN, Nat.cast_sub hrd]
          nlinarith
        exact_mod_cast hreal
  unfold retainedCoordinateRatio agreementIncidenceRatio
  rw [hden]
  have hdenOne : (0 : ℝ) < (d - r + 1 : ℕ) := by positivity
  have hdenTheta : (0 : ℝ) < (d : ℕ) := by positivity
  change ((n - uniformFirstOrderMCASplit D A + 1 : ℕ) : ℝ) /
      (d - r + 1 : ℕ) ≤ (42 / 41 : ℝ) * ((N : ℝ) / d)
  rw [show (42 / 41 : ℝ) * ((N : ℝ) / d) =
    ((42 * N : ℕ) : ℝ) / ((41 * d : ℕ) : ℝ) by push_cast; ring]
  apply (div_le_div_iff₀ hdenOne (by positivity : (0 : ℝ) < (41 * d : ℕ))).2
  exact_mod_cast (by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcross)

/-- At the one-forty-second split, the generic-fiber ratio costs at most
`42` times the direct agreement ratio. -/
theorem uniformFirstOrderMCASplit_fixedCoordinateRatio_le {n D A : ℕ}
    (hDA : D < A) :
    fixedCoordinateRatio n D (uniformFirstOrderMCASplit D A) ≤
      42 * agreementIncidenceRatio n D A := by
  let d := A - D
  let N := n - D
  let r := (d + 41) / 42
  obtain ⟨hr, hrd, hdr, _⟩ := uniformFirstOrderMCASplit_offset_bounds hDA
  have hL : uniformFirstOrderMCASplit D A = D + r := by
    simp only [uniformFirstOrderMCASplit, r, d]
  have hden : uniformFirstOrderMCASplit D A - D = r := by rw [hL]; omega
  unfold fixedCoordinateRatio agreementIncidenceRatio
  rw [hden]
  have hrR : (0 : ℝ) < (r : ℕ) := by positivity
  have hdR : (0 : ℝ) < (d : ℕ) := by
    dsimp only [d]
    exact_mod_cast (show 0 < A - D by omega)
  change ((N : ℕ) : ℝ) / r ≤ 42 * ((N : ℝ) / d)
  rw [show (42 : ℝ) * ((N : ℝ) / d) = ((42 * N : ℕ) : ℝ) / d by
    push_cast
    ring]
  apply (div_le_div_iff₀ hrR hdR).2
  exact_mod_cast (show (n - D) * d ≤ 42 * (n - D) * r by
    simpa only [d, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left (n - D) hdr)

/-- The direct agreement ratio is at most `25/6` in the gap-`6/25` regime. -/
theorem uniformFirstOrderMCA_agreementIncidenceRatio_le {n D A : ℕ} (hDA : D < A)
    (hgap : 25 * D + 6 * n ≤ 25 * A) :
    agreementIncidenceRatio n D A ≤ 25 / 6 := by
  have hden : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast (show 0 < A - D by omega)
  unfold agreementIncidenceRatio
  apply (div_le_iff₀ hden).2
  have hnum : ((n - D : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n D
  have hgapR : (6 : ℝ) * n ≤ 25 * (A - D : ℕ) := by
    exact_mod_cast (show 6 * n ≤ 25 * (A - D) by omega)
  norm_num
  nlinarith

/-- The degree-weighted agreement ratio is at most `25n/24`. -/
theorem uniformFirstOrderMCA_degree_mul_agreementIncidenceRatio_le {n D A : ℕ} (hDA : D < A)
    (hAn : A ≤ n) (hgap : 25 * D + 6 * n ≤ 25 * A) :
    D * agreementIncidenceRatio n D A ≤ (25 / 24 : ℝ) * n := by
  have hDn : D ≤ n := hDA.le.trans hAn
  have hden : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast (show 0 < A - D by omega)
  unfold agreementIncidenceRatio
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  have hgapR : (6 : ℝ) * n ≤ 25 * (A - D : ℕ) := by
    exact_mod_cast (show 6 * n ≤ 25 * (A - D) by omega)
  have hDcast : ((n - D : ℕ) : ℝ) = n - D := by
    rw [Nat.cast_sub hDn]
  rw [hDcast]
  have hsquare : (0 : ℝ) ≤ (2 * D - n) ^ 2 := sq_nonneg _
  nlinarith

set_option maxHeartbeats 2000000 in
-- The exact four-stage and rational-coefficient normalization exceeds the default budget.
/-- At the one-forty-second retention split, every actual derivative degree at most four has
raw exceptional charge at most `1304562211/984 * n²`.  The rational coefficient is strictly
below the public integral ceiling `1325775`. -/
theorem uniformFirstOrderMCA_exceptionCharge_le
    {n D A e : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hgap : 25 * D + 6 * n ≤ 25 * A) (he : e ≤ 4) :
    firstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A 276 23 e
        (uniformFirstOrderMCASplit D A) ≤
      (1304562211 / 984 : ℝ) * (n : ℝ) ^ 2 := by
  let theta := agreementIncidenceRatio n D A
  let L := uniformFirstOrderMCASplit D A
  have hthetaOne : 1 ≤ theta := by
    simpa only [theta] using one_le_agreementIncidenceRatio hDA hAn
  have htheta : 0 ≤ theta := le_trans zero_le_one hthetaOne
  have hthetaTop : theta ≤ 25 / 6 := by
    simpa only [theta] using uniformFirstOrderMCA_agreementIncidenceRatio_le hDA hgap
  have hDtheta : (D : ℝ) * theta ≤ (25 / 24 : ℝ) * n := by
    simpa only [theta] using uniformFirstOrderMCA_degree_mul_agreementIncidenceRatio_le hDA hAn hgap
  have hlambdaOne : retainedCoordinateRatio n A L ≤ (42 / 41 : ℝ) * theta := by
    simpa only [L, theta] using uniformFirstOrderMCASplit_retainedCoordinateRatio_le hDA hAn
  have hlambdaTwo : fixedCoordinateRatio n D L ≤ 42 * theta := by
    simpa only [L, theta] using uniformFirstOrderMCASplit_fixedCoordinateRatio_le hDA
  have htail : n - L ≤ n := Nat.sub_le n L
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnSquareFour : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnTwice : (2 : ℝ) * n ≤ (n : ℝ) ^ 2 := by nlinarith
  have hordinary : ordinaryTailCharge theta n D 276 (23 - e) ≤
      (399671 / 24 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      ordinaryTailCharge theta n D 276 (23 - e) ≤
          ordinaryTailCharge theta n D 276 23 :=
      ordinaryTailCharge_le htheta (Nat.sub_le _ _)
      _ = (45 : ℝ) * 276 + theta * (276 + 23 + 4 * D * 23 * 276) +
          (n - D - 1 : ℕ) * 23 := by
        simp only [ordinaryTailCharge, ite_eq_right (by norm_num : (23 : ℕ) ≠ 0)]
        norm_num
      _ ≤ (399671 / 24 : ℝ) * (n : ℝ) ^ 2 := by
        have hconstant : (45 : ℝ) * 276 ≤
            ((45 : ℝ) * 276 / 4) * (n : ℝ) ^ 2 := by nlinarith
        have hsmall : theta * ((276 + 23 : ℕ) : ℝ) ≤
            (((276 + 23 : ℕ) : ℝ) * (25 / 6 : ℝ) / 4) *
              (n : ℝ) ^ 2 := by
          have hfirst : theta * ((276 + 23 : ℕ) : ℝ) ≤
              (25 / 6 : ℝ) * ((276 + 23 : ℕ) : ℝ) := by gcongr
          norm_num at hfirst ⊢
          nlinarith
        have hdegree : theta * ((4 * D * 23 * 276 : ℕ) : ℝ) ≤
            ((23 : ℝ) * 276 * (25 / 6 : ℝ) / 2) * (n : ℝ) ^ 2 := by
          have hlinear : (4 : ℝ) * 23 * 276 * ((D : ℝ) * theta) ≤
              (4 : ℝ) * 23 * 276 * ((25 / 24 : ℝ) * n) := by gcongr
          push_cast
          norm_num at hlinear ⊢
          nlinarith
        have hlastCast : (((n - D - 1 : ℕ) : ℝ)) ≤ n := by
          exact_mod_cast (show n - D - 1 ≤ n from Nat.sub_le n (D + 1))
        have hlast : (((n - D - 1 : ℕ) : ℝ)) * 23 ≤
            (23 / 2 : ℝ) * (n : ℝ) ^ 2 := by
          have : (((n - D - 1 : ℕ) : ℝ)) * 23 ≤ (n : ℝ) * 23 := by gcongr
          nlinarith
        ring_nf at hconstant hsmall hdegree hlast ⊢
        linarith
  have hJNat : regularJointStageSum D 276 23 e ≤ 1149264 * D ^ 2 := by
    by_cases hDone : D = 1
    · subst D
      calc
        regularJointStageSum 1 276 23 e ≤ regularJointStageSum 1 276 23 4 := by
          exact regularJointStageSum_mono he (by norm_num)
        _ = 1276 := uniformFirstOrderMCA_regularJointStageSum_four_one
        _ ≤ 1149264 * 1 ^ 2 := by norm_num
    · have hDtwo : 2 ≤ D := by omega
      calc
        regularJointStageSum D 276 23 e ≤ regularJointStageSum D 276 23 4 := by
          exact regularJointStageSum_mono he (by norm_num)
        _ = 1149264 * (D - 2) ^ 2 + 1418984 * (D - 2) + 423252 :=
          uniformFirstOrderMCA_regularJointStageSum_four D hDtwo
        _ ≤ 1149264 * D ^ 2 := by
          obtain ⟨d, rfl⟩ : ∃ d, D = d + 2 := ⟨D - 2, by omega⟩
          norm_num
          have hid :
              1149264 * (d + 2) ^ 2 =
                (1149264 * d ^ 2 + 1418984 * d + 423252) +
                  (3178072 * d + 4173804) := by ring
          rw [hid]
          omega
  have hJ : (regularJointStageSum D 276 23 e : ℝ) ≤ 1149264 * (D : ℝ) ^ 2 := by
    exact_mod_cast hJNat
  have hjoint : retainedCoordinateRatio n A L * theta * regularJointStageSum D 276 23 e ≤
      (104750625 / 82 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      retainedCoordinateRatio n A L * theta * regularJointStageSum D 276 23 e ≤
          ((42 / 41 : ℝ) * theta) * theta *
            (1149264 * (D : ℝ) ^ 2) := by gcongr
      _ = (42 / 41 : ℝ) * 1149264 * (((D : ℝ) * theta) ^ 2) := by ring
      _ ≤ (42 / 41 : ℝ) * 1149264 * (((25 / 24 : ℝ) * n) ^ 2) := by
        gcongr
      _ = (104750625 / 82 : ℝ) * (n : ℝ) ^ 2 := by ring
  have hBNat : regularFiberStageSum D 23 e ≤ 724 * D := by
    by_cases hDone : D = 1
    · subst D
      calc
        regularFiberStageSum 1 23 e ≤ regularFiberStageSum 1 23 4 := by
          exact regularFiberStageSum_mono hD he (by norm_num)
        _ = 86 := uniformFirstOrderMCA_regularFiberStageSum_four_one
        _ ≤ 724 * 1 := by norm_num
    · have hDtwo : 2 ≤ D := by omega
      calc
        regularFiberStageSum D 23 e ≤ regularFiberStageSum D 23 4 := by
          exact regularFiberStageSum_mono hD he (by norm_num)
        _ = 724 * (D - 2) + 486 := uniformFirstOrderMCA_regularFiberStageSum_four D hDtwo
        _ ≤ 724 * D := by omega
  have hB : (regularFiberStageSum D 23 e : ℝ) ≤ 724 * (D : ℝ) := by exact_mod_cast hBNat
  have hlambdaTwo0 : 0 ≤ fixedCoordinateRatio n D L := by
    unfold fixedCoordinateRatio
    positivity
  have hfiber : ((n - L : ℕ) : ℝ) * fixedCoordinateRatio n D L * regularFiberStageSum D 23 e ≤
      (31675 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      ((n - L : ℕ) : ℝ) * fixedCoordinateRatio n D L * regularFiberStageSum D 23 e ≤
          (n : ℝ) * (42 * theta) * (724 * (D : ℝ)) := by
        gcongr
      _ = 42 * 724 * (n : ℝ) * ((D : ℝ) * theta) := by ring
      _ ≤ 42 * 724 * (n : ℝ) * ((25 / 24 : ℝ) * n) := by gcongr
      _ = (31675 : ℝ) * (n : ℝ) ^ 2 := by ring
  unfold firstOrderExceptionCharge
  calc
    _ ≤ (399671 / 24 : ℝ) * (n : ℝ) ^ 2 +
          (104750625 / 82 : ℝ) * (n : ℝ) ^ 2 +
          (31675 : ℝ) * (n : ℝ) ^ 2 := by
      simpa only [theta, L] using add_le_add (add_le_add hordinary hjoint) hfiber
    _ = (1304562211 / 984 : ℝ) * (n : ℝ) ^ 2 := by ring

/-- Integral-ceiling form of `uniformFirstOrderMCA_exceptionCharge_le`, used by the public
line-MCA facade. -/
theorem uniformFirstOrderMCA_exceptionCharge_le_ceiling
    {n D A e : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hgap : 25 * D + 6 * n ≤ 25 * A) (he : e ≤ 4) :
    firstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A 276 23 e
        (uniformFirstOrderMCASplit D A) ≤
      1325775 * (n : ℝ) ^ 2 := by
  apply (uniformFirstOrderMCA_exceptionCharge_le hn hD hDA hAn hgap he).trans
  gcongr
  norm_num

/-- The optimized max/min exceptional charge inherits the same integral ceiling.  This is the
numerical interface consumed by the squarefree semantic transfer. -/
theorem uniformFirstOrderMCA_optimizedExceptionCharge_le_ceiling
    {n D A : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hgap : 25 * D + 6 * n ≤ 25 * A) :
    maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A 276 23 4 ≤
      1325775 * (n : ℝ) ^ 2 := by
  classical
  unfold maxMinFirstOrderExceptionCharge
  apply Finset.max'_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  have heFour : e ≤ 4 := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using he
  apply le_trans ?_ (uniformFirstOrderMCA_exceptionCharge_le_ceiling
    hn hD hDA hAn hgap heFour)
  simp only [minFirstOrderExceptionCharge, hDA, ↓reduceDIte]
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  refine ⟨uniformFirstOrderMCASplit D A, ?_, rfl⟩
  obtain ⟨hDL, hLA⟩ := uniformFirstOrderMCASplit_bounds hDA
  simp only [Finset.mem_Icc]
  exact ⟨by omega, hLA⟩

end ReedSolomon.HiddenDerivative
