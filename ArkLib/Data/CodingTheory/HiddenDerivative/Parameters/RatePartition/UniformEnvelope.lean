/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformGamma

/-!
# Uniform finite-parameter envelopes for rate partition

For every actual code rate, the interpolation ambient degree and scalar parameters can be chosen
from the gap and block length alone. The resulting closed-multiplicity finite ratio exceeds
`151/150` while retaining the actual message dimension and agreement count in the bounds.

## Main definitions

* `UniformRatePartitionEnvelope`: an ambient degree and scalar parameters with the required guards.

## Main statements

* `exists_uniformRatePartitionEnvelope`: the envelope exists when the gap and block length satisfy
  the stated bounds.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- A choice of interpolation degree, rate and agreement parameters meeting the rate-partition
  guards at block length `n`. -/
structure UniformRatePartitionEnvelope (δ : ℝ) (n k A : ℕ) where
  /-- The selected interpolation ambient degree. -/
  ambientDegree : ℕ
  /-- The rate used by the partition estimate. -/
  rate : ℝ
  /-- The agreement parameter used by the partition estimate. -/
  agreement : ℝ
  /-- The selected rate is positive. -/
  rate_pos : 0 < rate
  /-- The selected rate is strictly below the agreement parameter. -/
  rate_lt_agreement : rate < agreement
  /-- The agreement parameter is at most one. -/
  agreement_le_one : agreement ≤ 1
  /-- The ambient degree exceeds the uniform derivative order. -/
  order_le : uniformDerivativeOrder δ + 1 ≤ ambientDegree
  /-- The ambient degree is below the block length. -/
  ambient_le : ambientDegree + 1 ≤ n
  /-- The message dimension fits in the ambient degree. -/
  message_le : k ≤ ambientDegree + 1
  /-- The ambient degree is at least `δ² n`. -/
  ambient_lower : δ ^ 2 * n ≤ ambientDegree
  /-- The rate covers the ambient degree. -/
  rate_upper : (ambientDegree : ℝ) ≤ rate * n
  /-- The agreement parameter is at most the actual agreement count divided by `n`. -/
  agreement_lower : agreement * n ≤ A
  /-- The finite ratio at the uniform multiplicity exceeds `151/150`. -/
  ratio_gt : (151 / 150 : ℝ) <
    partitionFiniteRatio rate agreement (uniformDerivativeOrder δ) (uniformMultiplicity δ)

private theorem finiteRatio_gt_of_uniformRateGamma {δ rate agreement : ℝ}
    (horder : 500 ≤ uniformDerivativeOrder δ) (hrate : 0 < rate)
    (hrateAgreement : rate ≤ agreement)
    (hgamma : (151 / 150 : ℝ) <
      rateGamma rate agreement (uniformDerivativeOrder δ) * Real.exp (-1 / 1000)) :
    (151 / 150 : ℝ) <
      partitionFiniteRatio rate agreement (uniformDerivativeOrder δ) (uniformMultiplicity δ) := by
  have hd : 0 < uniformDerivativeOrder δ := by omega
  have hscale : 1 < 1000 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    have hd' : (500 : ℝ) ≤ uniformDerivativeOrder δ := by exact_mod_cast horder
    nlinarith [sq_nonneg (uniformDerivativeOrder δ : ℝ)]
  have hloss := closedMultiplicityLoss_thousand_lt (by omega : 6 ≤ uniformDerivativeOrder δ)
  have hfinite := partitionFiniteRatio_closedMultiplicity_gt
    (rate := rate) (agreement := agreement) (scale := 1000) (η := 1 / 1000)
    (order := uniformDerivativeOrder δ) hrate hrateAgreement hscale hloss
  have hexp : (-1 / 1000 : ℝ) = -(1 / 1000 : ℝ) := by ring
  rw [hexp] at hgamma
  have hgamma0 : (151 / 150 : ℝ) <
      rateGamma rate agreement (uniformDerivativeOrder δ) * Real.exp (-(1 / 1000 : ℝ)) := by
    exact hgamma
  have hgamma' : (151 / 150 : ℝ) <
      (27 / 20 : ℝ) * rate * (uniformDerivativeOrder δ + 1) *
        Real.exp (-(rate / agreement *
          Real.log (6 * (uniformDerivativeOrder δ : ℝ)))) * Real.exp (-(1 / 1000 : ℝ)) := by
    rw [← rateGamma_eq_exp rate agreement hd]
    exact hgamma0
  have hfinite' : (27 / 20 : ℝ) * rate * (uniformDerivativeOrder δ + 1) *
      Real.exp (-(rate / agreement *
        Real.log (6 * (uniformDerivativeOrder δ : ℝ)))) * Real.exp (-(1 / 1000 : ℝ)) <
      partitionFiniteRatio rate agreement (uniformDerivativeOrder δ) (uniformMultiplicity δ) := by
    simpa only [uniformMultiplicity] using hfinite
  exact hgamma'.trans hfinite'

/-- Choose a finite interpolation envelope uniformly in the actual code rate. At high rate the
ambient degree is the message dimension and the scalar parameters are `R = k/n`, `a = R + δ`.
At low rate the ambient degree is `⌊2δ²n⌋₊` and the scalar parameters are `R = 2δ²`, `a = δ`. -/
theorem exists_uniformRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformBlockThreshold δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (UniformRatePartitionEnvelope δ n k A) := by
  have hδone : δ < 1 := by linarith
  have hd500 := uniformDerivativeOrder_ge_500 hδ hδsmall
  have hmorder := add_two_le_uniformMultiplicity δ
  have hm : 0 < uniformMultiplicity δ := by omega
  obtain ⟨hsize, _hmn, _hν, _hνn⟩ :=
    uniformBlockThreshold_guards hδ hδone.le hn
  have hkA : k ≤ A := by
    have : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast this
  have hnpos : 0 < n := hk.trans_le (hkA.trans hAn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  by_cases hhigh : δ ^ 2 * n ≤ k
  · let R : ℝ := (k : ℝ) / n
    let a : ℝ := R + δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [a]; linarith
    have hRlow : δ ^ 2 ≤ R := by
      dsimp [R]
      exact (le_div_iff₀ hnR).2 (by simpa only [Nat.cast_ofNat] using hhigh)
    have hRtop : R ≤ 1 - δ := by
      dsimp [R]
      apply (div_le_iff₀ hnR).2
      have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
      nlinarith
    have hmSize : (uniformMultiplicity δ : ℝ) ≤ δ ^ 2 * n := by linarith
    obtain ⟨horder, hambient⟩ := high_rate_ambient_guards hδ.le hmorder hmSize
      hhigh hgap hAn
    have hrateUpper : (k : ℝ) ≤ R * n := by
      dsimp [R]
      field_simp
      exact le_rfl
    have hagreementLower : a * n ≤ A := by
      calc
        a * n = (k : ℝ) + δ * n := by dsimp [a, R]; field_simp
        _ ≤ A := hgap
    have hgamma := uniformRateGamma_high_gt hδ hδsmall hRlow hRtop
    have hratio := finiteRatio_gt_of_uniformRateGamma hd500 hRpos (le_of_lt hRa) hgamma
    refine ⟨⟨k, R, a, hRpos, hRa, ?_, horder, hambient, Nat.le_succ k,
      hhigh, hrateUpper, hagreementLower, hratio⟩⟩
    dsimp [a]
    linarith
  · let D : ℕ := ⌊2 * δ ^ 2 * n⌋₊
    let R : ℝ := 2 * δ ^ 2
    let a : ℝ := δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [R, a]; nlinarith
    have hmSize : (uniformMultiplicity δ : ℝ) ≤ δ ^ 2 * n := by linarith
    obtain ⟨horder, hDlower, hambient⟩ := low_rate_padded_ambient_guards hδ.le
      (by linarith) hmorder hmSize
    have hkDreal : (k : ℝ) ≤ D := by
      have hklt : (k : ℝ) < δ ^ 2 * n := lt_of_not_ge hhigh
      exact hklt.le.trans (by simpa only [D] using hDlower)
    have hkD : k ≤ D := by exact_mod_cast hkDreal
    have hrateUpper : (D : ℝ) ≤ R * n := by
      dsimp [D, R]
      exact Nat.floor_le (by positivity)
    have hagreementLower : a * n ≤ A := by
      dsimp [a]
      nlinarith [Nat.cast_nonneg k (α := ℝ)]
    have hgamma := uniformRateGamma_low_gt hδ hδsmall
    have hratio := finiteRatio_gt_of_uniformRateGamma hd500 hRpos (le_of_lt hRa) hgamma
    refine ⟨⟨D, R, a, hRpos, hRa, hδone.le, horder, hambient,
      hkD.trans (Nat.le_succ D), hDlower, hrateUpper, hagreementLower, hratio⟩⟩

end ReedSolomon.HiddenDerivative.RatePartition
