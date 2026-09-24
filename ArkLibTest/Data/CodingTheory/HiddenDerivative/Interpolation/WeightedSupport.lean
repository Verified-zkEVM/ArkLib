/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Estimate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Interpolation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Weighted-support acceptance cases

Concrete eligibility, dimension, probability, interpolation, rank, residual, volume, and moment
instances for the weighted-support statements.
-/

open Finset MeasureTheory Set MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.WeightedSupportParameters
open scoped BigOperators ProbabilityTheory

example : WeightedSupportEligible 2 2 1 4
    ((jetExponentCoordinatesEquiv (d := 2) (by norm_num)).symm (1, 0, 0, fun _ => 1)) :=
  (weightedSupportEligible_coordinates_iff (by norm_num) 1 0 0 _).mpr ⟨by decide, by norm_num⟩

example : 5 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 2 1 2 one_pos) := by
  refine le_trans (le_of_eq ?_) (sum_count_le_finrank_weightedSupportSpace ℚ (d := 2) (W := 1)
    (L := 2) (by norm_num) one_pos)
  have hs : natWeightedSimplex (fun i : Fin (2 - 1) => i.val + 1) 1 = {fun _ => 0, fun _ => 1} := by
    decide
  have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by exact_mod_cast Nat.ceil_natCast 1
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  rw [hs, sum_pair (by decide)]
  norm_num [CubicStaircase.count, h1, h2, Finset.sum_range_succ]

example : 5 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 3 one_pos) := by
  have h := weightedSupport_dimension_ge_cubic_sum ℚ (d := 1) (W := 0) (L := 3) (by norm_num)
    one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by decide
  rw [hs, sum_singleton] at h
  norm_num at h
  have h4 : (4 : ℝ) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 3 one_pos) := by linarith
  exact_mod_cast h4

example : 21 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 5 16 one_pos) := by
  have h := weighted_dimension_probability ℚ (d := 1) (D := 1) (W := 5) (by norm_num) one_pos 1 8
    (by norm_num [harmonic])
  have hS : weightedSimplex (fun i : Fin (1 - 1) ↦ (i : ℝ) + 1) (5 : ℕ) = univ := by
    ext u
    simp [mem_weightedSimplex]
  have havg : ⨍ u in weightedSimplex (fun i : Fin (1 - 1) ↦ (i : ℝ) + 1) (5 : ℕ),
      (max (5 / 8 - normalizedRadius (5 : ℕ) (1 * 8) u) 0) ^ 3 = (5 / 8 : ℝ) ^ 3 := by
    rw [hS, Measure.restrict_univ]
    simp [normalizedRadius]
    norm_num
  rw [havg, show (8 : ℝ) * ((1 : ℕ) : ℝ) * (1 + 1) = 16 by norm_num] at h
  norm_num at h
  have h20 : (20 : ℝ) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 5 16 one_pos) := by linarith
  exact_mod_cast h20

example :
    let δ : ℝ := 1 / 4
    let d := ⌈Real.exp (xi / δ)⌉₊
    let H : ℝ := harmonic (d - 1)
    let g := rateGap δ (((2 : ℕ) : ℝ) / (4 : ℕ))
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊(1 + theta * g) * d * m / H⌋₊
    (543 / 500 : ℝ) * (4 : ℕ) * Module.finrank (ZMod 2) (LinearMap.range
      (weightedSupportLocalConstraint (R := ZMod 2) (d := d) (W := W)
        (L := (m : ℝ) * (2 : ℕ) * (1 + g)) m (show 0 < 2 by norm_num) 0 0)) <
      Module.finrank (ZMod 2)
        (weightedSupportSpace (ZMod 2) 2 d W ((m : ℝ) * (2 : ℕ) * (1 + g)) (by norm_num)) :=
  prescribed_weightedSupport_margin (1 / 4) 4 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : 2 * Real.exp 1 < 6 := by
  have h := normalized_rank_lt_of_rounding_bounds (2 * Real.exp 1) 1 1 1 1 1 0 2 3 1 1 1 1 1
    one_pos one_pos le_rfl le_rfl zero_le_one one_pos one_pos one_pos one_pos
    (by simp) (by norm_num) (by simpa using Real.exp_one_lt_d9.trans (by norm_num))
    (by norm_num) (by norm_num; ring_nf; exact le_rfl)
  norm_num at h
  exact h

example : (3 / 2 : ℝ) < (151 / (151 + 1)) * (38 / 25 - 1 ^ 2 / 151) := by
  exact weightedSupport_variance_factor_gt (d := 151) (H := 1) (H₂ := 38 / 25)
    (by norm_num) (by norm_num) (by norm_num)

example :
    (2 : ℝ) * (2 ^ 2 * 1 - 3 * 2 * 1 * (1 / 2) + 2 * 1 ^ 3) / ((2 + 1) * (2 + 2)) ≤
      2 * (1 + 2 * 1 ^ 3 / 2 ^ 2) := by
  exact weightedSupport_third_factor_le (d := 2) (H := 1) (H₂ := 1 / 2) (H₃ := 1)
    (by positivity) (by positivity) (by positivity) (by positivity)

example : (2 * ((12021 / 10000 : ℝ) + 2 * (1 / 10 : ℝ) ^ 3 / 1 ^ 2)) ≤ 241 / 100 := by
  have h := weightedSupport_third_factor_numeric (d := 1) (H := 1 / 10)
    (H₃ := 12021 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

example :
    ((1 : ℕ) : ℝ) ^ (10000 - 1) / ((10000 - 1).factorial : ℝ) ^ 2 *
        ((1 : ℕ) : ℝ) / 6 * (1 * 1) ^ 3 *
        ((5 / 8) ^ 3 + (4147 / 2160) *
          (((1 : ℕ) : ℝ) / (((10000 : ℕ) : ℝ) * (1 * 1))) ^ 2) ≤
      Module.finrank ℚ (weightedSupportSpace ℚ 1 10000 1 2 one_pos) := by
  have hharmonic : (harmonic 9999 : ℝ) ≤ 9999 := by
    calc
      (harmonic 9999 : ℝ) ≤ 1 + Real.log 9999 := harmonic_le_one_add_log _
      _ ≤ 1 + ((9999 : ℝ) - 1) := by
        have hlog : Real.log (9999 : ℝ) ≤ 9999 - 1 :=
          Real.log_le_sub_one_of_pos (x := 9999) (by norm_num)
        linarith
      _ = 9999 := by norm_num
  have hmean' : (harmonic 9999 : ℝ) / ((10000 : ℕ) : ℝ) ≤ 11 / 8 := by
    nlinarith [hharmonic]
  have hmean : ((1 : ℕ) : ℝ) * (harmonic (10000 - 1) : ℝ) / ((10000 : ℕ) : ℝ) ≤
      (1 + 3 * (1 : ℝ) / 8) * 1 := by
    rw [show (10000 : ℕ) - 1 = 9999 by omega, Nat.cast_one, one_mul]
    have hconst : (1 : ℝ) + 3 * 1 / 8 = 11 / 8 := by norm_num
    rw [hconst, mul_one]
    exact hmean'
  have hratio : ((1 : ℕ) : ℝ) / ((10000 : ℕ) * (1 * 1)) ≤ 10 / 27 := by norm_num
  have h := weighted_dimension_lower (F := ℚ) (D := 1) (d := 10000) (W := 1)
    (by norm_num) (by norm_num) (1 : ℝ) 1 hmean hratio
  have hcutoff : (1 : ℝ) * ((1 : ℕ) : ℝ) * (1 + 1) = 2 := by norm_num
  rw [hcutoff] at h
  exact h

private theorem eightLeCardWeightedSupportExponents :
    8 ≤ #(weightedSupportExponents 2 1 0 4 two_pos) := by
  refine le_trans (le_of_eq ?_) (sum_count_le_card_weightedSupportExponents (d := 1) (W := 0)
    (L := 4) one_pos two_pos)
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by decide
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  have h4 : ⌈(4 : ℝ)⌉₊ = 4 := by exact_mod_cast Nat.ceil_natCast 4
  rw [hs, sum_singleton]
  norm_num [CubicStaircase.count, h2, h4, Finset.sum_range_succ]

private theorem ceilFourDivTwo : ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ = 2 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

private theorem threePointSurplus :
    Fintype.card (Fin 3) * localResidualCoordinateBudget 1 1 0
        ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ < #(weightedSupportExponents 2 1 0 4 two_pos) := by
  have hceil := ceilFourDivTwo
  rw [hceil, show localResidualCoordinateBudget 1 1 0 2 = 2 by decide, Fintype.card_fin]
  exact (show 3 * 2 < 8 by norm_num).trans_le eightLeCardWeightedSupportExponents

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ weightedSupportSpace ℚ 2 1 0 4 two_pos ∧
      ∀ _ : Fin 3, SatisfiesLocalConstraints 1 0 0 Q :=
  exists_nonzero_weightedSupport_interpolant one_pos two_pos (fun _ : Fin 3 => (0 : ℚ))
    (fun _ : Fin 3 => (0 : ℚ)) threePointSurplus

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ exactInterpolationSpace ℚ 2 4 1 1 2 0 (by norm_num) ∧
      ∀ _ : Fin 3, SatisfiesLocalConstraints 1 0 0 Q := by
  exact exists_nonzero_exact_interpolant_of_weightedSupport_surplus
    (A := 4) (M := 2) (d := 1) (D := 2) (W := 0) (L := 4)
    (by norm_num) (by norm_num) (by norm_num) (fun _ : Fin 3 => (0 : ℚ)) (fun _ => 0)
    (by norm_num) (by norm_num) threePointSurplus

example : Module.finrank ℚ (LinearMap.range
    (weightedSupportLocalConstraint (D := 2) (d := 1) (W := 0) (L := 4) 2 (by norm_num)
      (0 : ℚ) (0 : ℚ))) ≤ 4 := by
  have hceil := ceilFourDivTwo
  have h := finrank_weightedSupportLocalConstraint_le (D := 2) (d := 1) (W := 0) (L := 4)
    (m := 2) one_pos (by norm_num) (0 : ℚ) (0 : ℚ)
  rw [hceil] at h
  exact h.trans (by decide)

private theorem ceilTwentyOneDivTen : ⌈(21 / 10 : ℝ)⌉₊ = 3 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

example :
    (localResidualCoordinateBudget 1 2 0 ⌈(21 / 10 : ℝ)⌉₊ : ℝ) = 6 ∧
      ∑ r ∈ range 2, (contactThreshold 2 2 r : ℝ) *
        ∑ z ∈ natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) (0 + r),
          (max ((21 / 10 : ℝ) - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) = 31 / 5 ∧
      (6 : ℝ) ≤ 31 / 5 := by
  have hb : localResidualCoordinateBudget 1 2 0 3 = 6 := by decide
  have h := localResidualCoordinateBudget_le_positivePart_sum 1 2 0 (21 / 10)
  have hc0 : contactThreshold 2 2 0 = 1 := by decide
  have hc1 : contactThreshold 2 2 1 = 1 := by decide
  simp only [ceilTwentyOneDivTen, hb, sum_range_succ,
    range_zero, sum_empty, Nat.reduceAdd, hc0, hc1,
    natWeightedSimplex] at h ⊢
  norm_num at h ⊢

example :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin 1 ↦ i.val + 1) 1,
        (max (1 - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) ≤
      (9 / 2 : ℝ) := by
  have hc : (((1 : ℕ) : ℝ) + ((1 + 1).choose 2 : ℕ)) * harmonic 1 /
      (((1 : ℕ) : ℝ) + 1) < 1 + ((1 : ℕ) : ℝ) := by
    norm_num [harmonic]
  have h := weighted_residual_sum_le_volume_mul_harmonic_variance 1 1 (T := 1) hc
  have hset : Finset.natWeightedSimplex (fun i : Fin 1 ↦ i.val + 1) 1 =
      {fun _ ↦ 0, fun _ ↦ 1} := by decide
  rw [hset, sum_pair (by decide)] at h ⊢
  rw [volume_real_weightedSimplex_succ 1 (by norm_num)] at h
  norm_num [harmonic, Fin.sum_univ_succ, Nat.choose] at h ⊢

example :
    (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (1 / 5) ^ 2 ≤
      ∫ x, (max (5 / 8 - x) 0) ^ 3 ∂
        ((2 : ENNReal)⁻¹ • (Measure.dirac (-1 : ℝ) + Measure.dirac 1)) := by
  set P : Measure ℝ := (2 : ENNReal)⁻¹ • (Measure.dirac (-1 : ℝ) + Measure.dirac 1)
  have hprob : IsProbabilityMeasure P := ⟨by
    simp only [P, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩
  have hdirac : ∀ (a : ℝ) (f : ℝ → ℝ), Integrable f (Measure.dirac a) :=
    fun a f ↦ integrable_dirac (by simp)
  have hint : ∀ f : ℝ → ℝ, Integrable f P := fun f ↦
    ((hdirac (-1) f).add_measure (hdirac 1 f)).smul_measure (by simp)
  have hP : ∀ f : ℝ → ℝ, ∫ x, f x ∂P = (f (-1) + f 1) / 2 := by
    intro f
    rw [integral_smul_measure, integral_add_measure (hdirac (-1) f) (hdirac 1 f),
      integral_dirac, integral_dirac]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  have hmean : ∫ x, x ∂P = 0 := by rw [hP]; norm_num
  have h := contribution_integral_lower P id (1 / 5) (hint _) (hint _) hmean
    (by norm_num) (by rw [hP]; norm_num) (by rw [hP]; norm_num)
  change (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (1 / 5) ^ 2 ≤
    ∫ x, (max (5 / 8 - x) 0) ^ 3 ∂P
  exact h

private def singletonDomain : Fin 1 ↪ ℚ where
  toFun _ := 0
  inj' i j _ := by
    apply Fin.ext
    omega

private def singletonCutoff : ℝ :=
  ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (1 + (1 : ℝ))

private theorem singletonLocalRank_le_two :
    Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) ≤ 2 := by
  calc
    _ ≤ localResidualCoordinateBudget 1 1 0 ⌈singletonCutoff / 1⌉₊ := by
      simpa using (finrank_weightedSupportLocalConstraint_le (F := ℚ) (d := 1) (D := 1)
        (W := 0) (L := singletonCutoff) (m := 1) (by norm_num) Nat.one_pos (0 : ℚ) 0)
    _ ≤ 2 := by
      norm_num [singletonCutoff, localResidualCoordinateBudget, contactThreshold,
        Finset.natWeightedSimplex]

private theorem singletonWeightedSupportDimension_ge_four :
    4 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 singletonCutoff Nat.one_pos) := by
  have h := sum_count_le_finrank_weightedSupportSpace ℚ (d := 1) (D := 1) (W := 0)
    (L := singletonCutoff) (by decide) Nat.one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by
    decide
  have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by exact_mod_cast Nat.ceil_natCast 1
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  rw [hs, sum_singleton] at h
  norm_num [singletonCutoff, CubicStaircase.count, h1, h2] at h
  exact h

/-- A concrete numerical bound for the dimension margin at cutoff two. -/
private theorem singletonFixedMarginAtTwo :
    (543 / 500 : ℝ) * ((1 : ℕ) : ℝ) * Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 singletonCutoff
          Nat.one_pos) := by
  have hrank : (Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) : ℝ) ≤ 2 := by
    exact_mod_cast singletonLocalRank_le_two
  have hdim : (4 : ℝ) ≤ Module.finrank ℚ
      (weightedSupportSpace ℚ 1 1 0 singletonCutoff Nat.one_pos) := by
    exact_mod_cast singletonWeightedSupportDimension_ge_four
  nlinarith

/-- One evaluation constraint admits a nonzero interpolant under the fixed dimension margin. -/
example : ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 ∧
    Q ∈ weightedSupportSpace ℚ 1 1 0 2 (by decide) ∧
    (∀ i : Fin 1, SatisfiesLocalConstraints 1 (singletonDomain i) 0 Q) ∧
    jetTotalDegree Q < 2 ∧ differentialWeightedDegree 1 Q < 2 := by
  have hD : 0 < (1 : ℕ) := by decide
  have hm : 0 < (1 : ℕ) := by decide
  have hA : 0 < (2 : ℕ) := by decide
  have hg : (1 : ℝ) ≤ 1 := by norm_num
  have hcut : ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (1 + (1 : ℝ)) ≤
      ((1 * 2 : ℕ) : ℝ) := by norm_num
  have hresult := @ReedSolomon.HiddenDerivative.exists_weightedSupport_interpolant_of_fixed_margin
    ℚ (inferInstance : Field ℚ) 1 1 1 0 1 2 (1 : ℝ) singletonDomain (fun _ => 0)
    hD hm hA hg hcut singletonFixedMarginAtTwo
  obtain ⟨Q, hQ, hsupport, hlocal, hdegree, hweight⟩ := hresult
  have hsupport' : Q ∈ weightedSupportSpace ℚ 1 1 0 2 (by decide) := by
    convert hsupport using 1; norm_num
  exact ⟨Q, hQ, hsupport', hlocal, hdegree, hweight⟩
