/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.ClosedRatio
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.UniformGamma

/-!
# A uniform interpolation envelope for each actual code rate

The high-rate branch keeps the actual message ambient degree. The low-rate branch pads it to
`floor(2*δ²*n)`. The envelope is chosen before the field and received words. Both mathematical
certificates and executable search witnesses use this same choice and retain the actual `k,A`
in their agreement gap.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- The finite ambient choice shared by the uniform list, MCA, and executed-decoding proofs. -/
structure UniformRatePartitionEnvelope (δ : ℝ) (n k A : ℕ) where
  ambientDegree : ℕ
  rate : ℝ
  agreement : ℝ
  rate_pos : 0 < rate
  rate_lt_agreement : rate < agreement
  agreement_le_one : agreement ≤ 1
  order_le : uniformRatePartitionOrder δ + 1 ≤ ambientDegree
  ambient_le : ambientDegree + 1 ≤ n
  message_le : k ≤ ambientDegree + 1
  ambient_lower : δ ^ 2 * n ≤ ambientDegree
  rate_upper : (ambientDegree : ℝ) ≤ rate * n
  agreement_lower : agreement * n ≤ A
  ratio_gt : (151 / 150 : ℝ) < ratePartitionFiniteRatio rate agreement
    (uniformRatePartitionOrder δ) (uniformRatePartitionMultiplicity δ)

/-- Choose the interpolation envelope uniformly in the actual code rate.  At high rate the
ambient degree is the message dimension and the scalar parameters are `R = k / n`, `a = R + δ`.
At low rate the ambient is padded to `floor (2δ²n)` and the scalar parameters are
`R = 2δ²`, `a = δ`. -/
theorem exists_uniformRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (UniformRatePartitionEnvelope δ n k A) := by
  have hδone : δ < 1 := by linarith
  have hd500 := uniformRatePartitionOrder_ge_500 hδ hδsmall
  have hmorder := ratePartitionClosedMultiplicity_ge_order hd500
  have hm : 0 < uniformRatePartitionMultiplicity δ := by
    exact lt_of_lt_of_le (by omega) hmorder
  obtain ⟨hsize, _hmn, _hν, _hνn⟩ :=
    uniformRatePartition_integer_guards hδ hδone hm hn
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
    obtain ⟨horder, hambient⟩ := uniformRatePartition_high_ambient
      hδ hδone hmorder hsize hhigh hgap hAn
    have hrateUpper : (k : ℝ) ≤ R * n := by
      dsimp [R]
      field_simp
      exact le_rfl
    have hagreementLower : a * n ≤ A := by
      calc
        a * n = (k : ℝ) + δ * n := by dsimp [a, R]; field_simp
        _ ≤ A := hgap
    have hgamma := uniformRatePartitionGamma_high_gt hδ hδsmall hRlow hRtop
    have hclosed := ratePartition_closed_ratio_gt hRpos hRa hd500
    refine ⟨⟨k, R, a, hRpos, hRa, ?_, horder, hambient, Nat.le_succ k,
      hhigh, hrateUpper, hagreementLower, ?_⟩⟩
    · dsimp [a]
      linarith
    · exact hgamma.trans (by
        rw [show (-1 / 1000 : ℝ) = -(1 / 1000 : ℝ) by ring]
        simpa only [R, a, uniformRatePartitionMultiplicity] using hclosed)
  · let D : ℕ := ⌊2 * δ ^ 2 * n⌋₊
    let R : ℝ := 2 * δ ^ 2
    let a : ℝ := δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [R, a]; nlinarith
    obtain ⟨horder, hDlower, hambient⟩ := uniformRatePartition_low_ambient
      hδ hδsmall hmorder hsize
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
    have hgamma := uniformRatePartitionGamma_low_gt hδ hδsmall
    have hclosed := ratePartition_closed_ratio_gt hRpos hRa hd500
    refine ⟨⟨D, R, a, hRpos, hRa, hδone.le, horder, hambient,
      hkD.trans (Nat.le_succ D), hDlower, hrateUpper, hagreementLower, ?_⟩⟩
    exact hgamma.trans (by
      rw [show (-1 / 1000 : ℝ) = -(1 / 1000 : ℝ) by ring]
      simpa only [R, a, uniformRatePartitionMultiplicity] using hclosed)

end ReedSolomon.HiddenDerivative
