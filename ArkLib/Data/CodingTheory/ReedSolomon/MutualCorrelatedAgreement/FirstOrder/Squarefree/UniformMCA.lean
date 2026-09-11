/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.Uniform
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.HybridConstants
/-!
# The height-276 first-order MCA certificate

The line-MCA support uses `(m, M, μ) = (12, 4, 23)`, separately from the
list support `(12, 4, 22)`.  The last shell has local rank zero but supplies
the challenge-height margin needed at height `276`.

The source has truncated degree blocks.  We retain exactly the active prefix
on each of the nine rate intervals cut out by `25 s k = 72 n`, for
`s = 4, ..., 11`.  Prefix accounting avoids replacing those truncated blocks
by a weaker global affine estimate.
-/

@[expose] public section

namespace ReedSolomon

open HiddenDerivative
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

/-- Prefix accounting for the truncated shifted source. -/
private theorem uniformFirstOrderMCA_shiftedHeightSlot_accounting
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

set_option maxHeartbeats 10000000 in
-- The nine exact interval branches require more than the default heartbeat budget.
/-- The support `(12, 4, 23)` has a strict shifted source surplus at height
`276` throughout the gap-`6/25` regime. -/
theorem uniformFirstOrderMCA_heightSlotCount (n k A : ℕ)
    (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : 25 * k + 6 * n ≤ 25 * A) :
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
  let sourceTerm := fun t ↦
    ∑ b ∈ Finset.range (min t 4 + 1),
      (12 * A + b - D * t) * (276 + 1 - t)
  have hpartial (q : ℕ) (hq : q ≤ 24) :
      (∑ t ∈ Finset.range q, sourceTerm t) ≤
        firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
    unfold firstOrderCurveShiftedHeightSlotCount
    simpa only [sourceTerm, Nat.one_mul, show 23 + 1 = 24 by norm_num] using
      (Finset.sum_le_sum_of_subset
        (Finset.range_mono hq) :
          (∑ t ∈ Finset.range q, sourceTerm t) ≤
            ∑ t ∈ Finset.range 24, sourceTerm t)
  apply hrow'.trans_lt
  by_cases h11 : 275 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 24 le_rfl)
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 24
    have hw : uniformFirstOrderMCAHeightWeightUpTo 24 = 29100 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 24 = 357890 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 24 = 55445 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h10 : 250 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 23 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 23
    have hw : uniformFirstOrderMCAHeightWeightUpTo 23 = 27830 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 23 = 328680 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 23 = 52905 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h9 : 225 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 22 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 22
    have hw : uniformFirstOrderMCAHeightWeightUpTo 22 = 26555 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 22 = 300630 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 22 = 50355 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h8 : 200 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 21 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 21
    have hw : uniformFirstOrderMCAHeightWeightUpTo 21 = 25275 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 21 = 273750 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 21 = 47795 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h7 : 175 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 20 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 20
    have hw : uniformFirstOrderMCAHeightWeightUpTo 20 = 23990 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 20 = 248050 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 20 = 45225 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h6 : 150 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 19 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 19
    have hw : uniformFirstOrderMCAHeightWeightUpTo 19 = 22700 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 19 = 223540 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 19 = 42645 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h5 : 125 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 18 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 18
    have hw : uniformFirstOrderMCAHeightWeightUpTo 18 = 21405 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 18 = 200230 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 18 = 40055 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h4 : 100 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 17 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 17
    have hw : uniformFirstOrderMCAHeightWeightUpTo 17 = 20105 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 17 = 178130 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 17 = 37455 := by decide
    rw [hw, ht, hj] at haccount
    omega
  · apply lt_of_lt_of_le ?_ (hpartial 16 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 16
    have hw : uniformFirstOrderMCAHeightWeightUpTo 16 = 18800 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 16 = 157250 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 16 = 34845 := by decide
    rw [hw, ht, hj] at haccount
    omega

/-- The height-276 support supplies precisely the ambient-degree, positive-budget,
message-degree, and shifted-slot hypotheses used by the semantic curve constructor. -/
theorem uniformFirstOrderMCA_parameters (n k A : ℕ)
    (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : 25 * k + 6 * n ≤ 25 * A) :
    let D := k - 1
    0 < D ∧ 0 < 12 * A ∧ k ≤ D + 1 ∧
      firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 <
        firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_⟩
  exact uniformFirstOrderMCA_heightSlotCount n k A hk hAn hgap

/-! ## Exact regular-stage arithmetic -/

set_option maxHeartbeats 2000000 in
-- Expanding the four exact cap-sensitive stages needs more than the default budget.
/-- Exact generic-fiber degree of the four regular stages. -/
theorem uniformFirstOrderMCA_hybridB1_four (D : ℕ) (hD : 1 ≤ D) :
    hybridB1 D 23 4 = 724 * D - 314 := by
  norm_num [hybridB1, Finset.sum_range_succ, hybridTau,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap,
    AffineHilbert.fixedFiberDerivativeImageDegree]
  omega

/-- Exact joint-family degree of the four regular stages. -/
theorem uniformFirstOrderMCA_hybridJ1_four (D : ℕ) (hD : 1 ≤ D) :
    hybridJ1 D 276 23 4 =
      1149264 * D ^ 2 - 1045144 * D + 236180 := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hrhs :
      1149264 * (d + 1) ^ 2 - 1045144 * (d + 1) =
        1149264 * d ^ 2 + 1253384 * d + 104120 := by
    have hid :
        1149264 * (d + 1) ^ 2 =
          (1149264 * d ^ 2 + 1253384 * d + 104120) +
            1045144 * (d + 1) := by ring
    have hle : 1045144 * (d + 1) ≤ 1149264 * (d + 1) ^ 2 := by
      rw [hid]
      omega
    exact (Nat.sub_eq_iff_eq_add hle).2 hid
  rw [hrhs]
  norm_num [hybridJ1, Finset.sum_range_succ,
    firstOrderCurveJointStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap, firstOrderCurveFiberStageOne,
    hybridTau, AffineHilbert.mixedDerivativeImageDegree,
    AffineHilbert.fixedFiberDerivativeImageDegree]
  have hτ : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
  simp only [hτ]
  have hm1 : d + 1 ≤ 1 + (2 * d + 1) * 19 := by omega
  have hm2 : 2 * d + 1 + (d + 1) ≤ 1 + (2 * d + 1) * 20 := by omega
  have hm3 : (2 * d + 1) * 2 + (d + 1) ≤ 1 + (2 * d + 1) * 21 := by omega
  have hm4 : (2 * d + 1) * 3 + (d + 1) ≤ 1 + (2 * d + 1) * 22 := by omega
  simp only [min_eq_right hm1, min_eq_right hm2, min_eq_right hm3,
    min_eq_right hm4]
  have hs1 : 1 + (2 * d + 1) * 19 - (d + 1) = 19 + 37 * d := by omega
  have hs2 : 1 + (2 * d + 1) * 20 - (2 * d + 1 + (d + 1)) =
      19 + 37 * d := by omega
  have hs3 : 1 + (2 * d + 1) * 21 - ((2 * d + 1) * 2 + (d + 1)) =
      19 + 37 * d := by omega
  have hs4 : 1 + (2 * d + 1) * 22 - ((2 * d + 1) * 3 + (d + 1)) =
      19 + 37 * d := by omega
  simp only [hs1, hs2, hs3, hs4]
  ring_nf
  have ha1 : 40 + d * 116 + d ^ 2 * 76 - (1 + d * 2 + d ^ 2) =
      39 + 114 * d + 75 * d ^ 2 := by omega
  have ha2 : 84 + d * 286 + d ^ 2 * 240 - (4 + d * 12 + d ^ 2 * 9) =
      80 + 274 * d + 231 * d ^ 2 := by omega
  have ha3 : 132 + d * 472 + d ^ 2 * 420 - (9 + d * 30 + d ^ 2 * 25) =
      123 + 442 * d + 395 * d ^ 2 := by omega
  have ha4 : 184 + d * 674 + d ^ 2 * 616 - (16 + d * 56 + d ^ 2 * 49) =
      168 + 618 * d + 567 * d ^ 2 := by omega
  simp only [ha1, ha2, ha3, ha4]
  ring

/-- The exact regular fiber sum is monotone in the actual derivative degree. -/
theorem hybridB1_mono {D μ e M : ℕ} (hD : 1 ≤ D)
    (heM : e ≤ M) (hMμ : M ≤ μ) : hybridB1 D μ e ≤ hybridB1 D μ M := by
  induction M generalizing e with
  | zero =>
      have : e = 0 := by omega
      subst e
      exact le_rfl
  | succ M ih =>
      by_cases heq : e = M + 1
      · subst e
        exact le_rfl
      · exact (ih (by omega) (by omega)).trans
          ((hybridB1_add_one_le_succ hD (by omega)).trans' (Nat.le_add_right _ _))

/-- The exact regular joint sum is monotone in the actual derivative degree. -/
theorem hybridJ1_mono {D h μ e M : ℕ} (heM : e ≤ M) (hMμ : M ≤ μ) :
    hybridJ1 D h μ e ≤ hybridJ1 D h μ M := by
  induction M generalizing e with
  | zero =>
      have : e = 0 := by omega
      subst e
      exact le_rfl
  | succ M ih =>
      by_cases heq : e = M + 1
      · subst e
        exact le_rfl
      · apply (ih (by omega) (by omega)).trans
        unfold hybridJ1
        rw [Finset.sum_range_succ]
        have hsum :
            (∑ i ∈ Finset.range M,
              firstOrderCurveJointStageOne (D + 1) 1 h (μ - i) (M - i)
                (hybridTau D)) ≤
              ∑ i ∈ Finset.range M,
                firstOrderCurveJointStageOne (D + 1) 1 h (μ - i) (M + 1 - i)
                  (hybridTau D) := by
          apply Finset.sum_le_sum
          intro i hi
          exact firstOrderCurveJointStageOne_mono_derivative (by omega) (by omega)
        exact hsum.trans (Nat.le_add_right _ _)

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
theorem uniformFirstOrderMCASplit_lambdaOne_le {n D A : ℕ}
    (hDA : D < A) (hAn : A ≤ n) :
    hybridLambdaOne n A (uniformFirstOrderMCASplit D A) ≤
      (42 / 41 : ℝ) * hybridTheta n D A := by
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
  unfold hybridLambdaOne hybridTheta
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
theorem uniformFirstOrderMCASplit_lambdaTwo_le {n D A : ℕ}
    (hDA : D < A) (_hAn : A ≤ n) :
    hybridLambdaTwo n D (uniformFirstOrderMCASplit D A) ≤
      42 * hybridTheta n D A := by
  let d := A - D
  let N := n - D
  let r := (d + 41) / 42
  obtain ⟨hr, hrd, hdr, _⟩ := uniformFirstOrderMCASplit_offset_bounds hDA
  have hL : uniformFirstOrderMCASplit D A = D + r := by
    simp only [uniformFirstOrderMCASplit, r, d]
  have hden : uniformFirstOrderMCASplit D A - D = r := by rw [hL]; omega
  unfold hybridLambdaTwo hybridTheta
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
theorem uniformFirstOrderMCA_theta_le {n D A : ℕ} (hDA : D < A)
    (_hAn : A ≤ n) (hgap : 25 * D + 6 * n ≤ 25 * A) :
    hybridTheta n D A ≤ 25 / 6 := by
  have hden : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast (show 0 < A - D by omega)
  unfold hybridTheta
  apply (div_le_iff₀ hden).2
  have hnum : ((n - D : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n D
  have hgapR : (6 : ℝ) * n ≤ 25 * (A - D : ℕ) := by
    exact_mod_cast (show 6 * n ≤ 25 * (A - D) by omega)
  norm_num
  nlinarith

/-- The degree-weighted agreement ratio is at most `25n/24`. -/
theorem uniformFirstOrderMCA_D_mul_theta_le {n D A : ℕ} (hDA : D < A)
    (hAn : A ≤ n) (hgap : 25 * D + 6 * n ≤ 25 * A) :
    D * hybridTheta n D A ≤ (25 / 24 : ℝ) * n := by
  have hDn : D ≤ n := hDA.le.trans hAn
  have hden : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast (show 0 < A - D by omega)
  unfold hybridTheta
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
theorem uniformFirstOrderMCA_hybridERaw_le
    {n D A e : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hgap : 25 * D + 6 * n ≤ 25 * A) (he : e ≤ 4) :
    hybridERaw (hybridTheta n D A) n D A 276 23 e
        (uniformFirstOrderMCASplit D A) ≤
      (1304562211 / 984 : ℝ) * (n : ℝ) ^ 2 := by
  let theta := hybridTheta n D A
  let L := uniformFirstOrderMCASplit D A
  have hthetaOne : 1 ≤ theta := by
    simpa only [theta] using hybridTheta_one_le hDA hAn
  have htheta : 0 ≤ theta := le_trans zero_le_one hthetaOne
  have hthetaTop : theta ≤ 25 / 6 := by
    simpa only [theta] using uniformFirstOrderMCA_theta_le hDA hAn hgap
  have hDtheta : (D : ℝ) * theta ≤ (25 / 24 : ℝ) * n := by
    simpa only [theta] using uniformFirstOrderMCA_D_mul_theta_le hDA hAn hgap
  have hlambdaOne : hybridLambdaOne n A L ≤ (42 / 41 : ℝ) * theta := by
    simpa only [L, theta] using uniformFirstOrderMCASplit_lambdaOne_le hDA hAn
  have hlambdaTwo : hybridLambdaTwo n D L ≤ 42 * theta := by
    simpa only [L, theta] using uniformFirstOrderMCASplit_lambdaTwo_le hDA hAn
  have htail : n - L ≤ n := Nat.sub_le n L
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnSquareFour : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnTwice : (2 : ℝ) * n ≤ (n : ℝ) ^ 2 := by nlinarith
  have hordinary : hybridOrdinaryRaw theta n D 276 (23 - e) ≤
      (399671 / 24 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      hybridOrdinaryRaw theta n D 276 (23 - e) ≤
          hybridOrdinaryRaw theta n D 276 23 :=
        hybridOrdinaryRaw_mono_to_top htheta (Nat.sub_le _ _) (by norm_num)
      _ = (45 : ℝ) * 276 + theta * (276 + 23 + 4 * D * 23 * 276) +
          (n - D - 1 : ℕ) * 23 := by
        simp only [hybridOrdinaryRaw, if_neg (by norm_num : (23 : ℕ) ≠ 0)]
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
  have hJNat : hybridJ1 D 276 23 e ≤ 1149264 * D ^ 2 := by
    have hsub : 236180 ≤ 1045144 * D := by omega
    have hlinear : 1045144 * D ≤ 1149264 * D ^ 2 := by
      calc
        1045144 * D ≤ 1149264 * D := Nat.mul_le_mul_right D (by norm_num)
        _ ≤ 1149264 * D ^ 2 := by
          gcongr
          nlinarith
    calc
      hybridJ1 D 276 23 e ≤ hybridJ1 D 276 23 4 := hybridJ1_mono he (by norm_num)
      _ = 1149264 * D ^ 2 - 1045144 * D + 236180 :=
        uniformFirstOrderMCA_hybridJ1_four D hD
      _ ≤ 1149264 * D ^ 2 - 1045144 * D + 1045144 * D := by gcongr
      _ = 1149264 * D ^ 2 := Nat.sub_add_cancel hlinear
  have hJ : (hybridJ1 D 276 23 e : ℝ) ≤ 1149264 * (D : ℝ) ^ 2 := by
    exact_mod_cast hJNat
  have hjoint : hybridLambdaOne n A L * theta * hybridJ1 D 276 23 e ≤
      (104750625 / 82 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      hybridLambdaOne n A L * theta * hybridJ1 D 276 23 e ≤
          ((42 / 41 : ℝ) * theta) * theta *
            (1149264 * (D : ℝ) ^ 2) := by gcongr
      _ = (42 / 41 : ℝ) * 1149264 * (((D : ℝ) * theta) ^ 2) := by ring
      _ ≤ (42 / 41 : ℝ) * 1149264 * (((25 / 24 : ℝ) * n) ^ 2) := by
        gcongr
      _ = (104750625 / 82 : ℝ) * (n : ℝ) ^ 2 := by ring
  have hBNat : hybridB1 D 23 e ≤ 724 * D := by
    calc
      hybridB1 D 23 e ≤ hybridB1 D 23 4 := hybridB1_mono hD he (by norm_num)
      _ = 724 * D - 314 := uniformFirstOrderMCA_hybridB1_four D hD
      _ ≤ 724 * D := Nat.sub_le _ _
  have hB : (hybridB1 D 23 e : ℝ) ≤ 724 * (D : ℝ) := by exact_mod_cast hBNat
  have hlambdaTwo0 : 0 ≤ hybridLambdaTwo n D L := by
    unfold hybridLambdaTwo
    positivity
  have hfiber : ((n - L : ℕ) : ℝ) * hybridLambdaTwo n D L * hybridB1 D 23 e ≤
      (31675 : ℝ) * (n : ℝ) ^ 2 := by
    calc
      ((n - L : ℕ) : ℝ) * hybridLambdaTwo n D L * hybridB1 D 23 e ≤
          (n : ℝ) * (42 * theta) * (724 * (D : ℝ)) := by
        gcongr
      _ = 42 * 724 * (n : ℝ) * ((D : ℝ) * theta) := by ring
      _ ≤ 42 * 724 * (n : ℝ) * ((25 / 24 : ℝ) * n) := by gcongr
      _ = (31675 : ℝ) * (n : ℝ) ^ 2 := by ring
  unfold hybridERaw
  calc
    _ ≤ (399671 / 24 : ℝ) * (n : ℝ) ^ 2 +
          (104750625 / 82 : ℝ) * (n : ℝ) ^ 2 +
          (31675 : ℝ) * (n : ℝ) ^ 2 := by
      simpa only [theta, L] using add_le_add (add_le_add hordinary hjoint) hfiber
    _ = (1304562211 / 984 : ℝ) * (n : ℝ) ^ 2 := by ring

/-- Integral-ceiling form of `uniformFirstOrderMCA_hybridERaw_le`, used by the public
line-MCA facade. -/
theorem uniformFirstOrderMCA_hybridERaw_le_ceiling
    {n D A e : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hgap : 25 * D + 6 * n ≤ 25 * A) (he : e ≤ 4) :
    hybridERaw (hybridTheta n D A) n D A 276 23 e
        (uniformFirstOrderMCASplit D A) ≤
      1325775 * (n : ℝ) ^ 2 := by
  apply (uniformFirstOrderMCA_hybridERaw_le hn hD hDA hAn hgap he).trans
  gcongr
  norm_num

/-- The optimized max/min exceptional charge inherits the same integral ceiling.  This is the
numerical interface consumed by the squarefree semantic transfer. -/
theorem uniformFirstOrderMCA_hybridEOptimizedRaw_le_ceiling
    {n D A : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hgap : 25 * D + 6 * n ≤ 25 * A) :
    hybridEOptimizedRaw (hybridTheta n D A) n D A 276 23 4 ≤
      1325775 * (n : ℝ) ^ 2 := by
  classical
  unfold hybridEOptimizedRaw
  apply Finset.max'_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  have heFour : e ≤ 4 := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using he
  apply le_trans ?_ (uniformFirstOrderMCA_hybridERaw_le_ceiling
    hn hD hDA hAn hgap heFour)
  simp only [hybridERawAtDegree, hDA, ↓reduceDIte]
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  refine ⟨uniformFirstOrderMCASplit D A, ?_, rfl⟩
  obtain ⟨hDL, hLA⟩ := uniformFirstOrderMCASplit_bounds hDA
  simp only [Finset.mem_Icc]
  exact ⟨by omega, hLA⟩

end ReedSolomon
