/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformGamma
public import Mathlib.Algebra.CharP.Algebra

/-!
# Uniform finite-parameter envelopes for rate partition

The derivative order depends on the gap, while the interpolation multiplicity may follow either
the executable or mathematical recipe. The envelope's ambient degree and scalar parameters may
depend on the actual message dimension. Its closed-multiplicity finite ratio exceeds `151/150`.

## Main statements

* `RatePartitionEnvelope`: an ambient degree and scalar parameters with guards for a supplied
  interpolation multiplicity.
* `exists_ratePartitionEnvelope`: the envelope exists from the multiplicity, size and ratio bounds.
* `exists_uniformRatePartitionEnvelope`: the executable recipe supplies those bounds.
* `uniformEnvelope_exactAgreementGuards`: the shared numerical and characteristic guards for
  uniform exact-agreement certificate endpoints.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- A choice of interpolation degree, rate and agreement parameters meeting the rate-partition
  guards at block length `n`. The multiplicity `m` is `uniformMultiplicity δ` for the executable
  recipe and `uniformMathematicalMultiplicity δ` for the mathematical recipe. -/
structure RatePartitionEnvelope (δ : ℝ) (m n k A : ℕ) where
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
  /-- The finite ratio at interpolation multiplicity `m` exceeds `151/150`. -/
  ratio_gt : (151 / 150 : ℝ) <
    partitionFiniteRatio rate agreement (uniformDerivativeOrder δ) m

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
    rw [← rateGamma_eq_exponential (rate := rate) (agreement := agreement)
      (order := uniformDerivativeOrder δ) hd]
    exact hgamma0
  have hfinite' : (27 / 20 : ℝ) * rate * (uniformDerivativeOrder δ + 1) *
      Real.exp (-(rate / agreement *
        Real.log (6 * (uniformDerivativeOrder δ : ℝ)))) * Real.exp (-(1 / 1000 : ℝ)) <
      partitionFiniteRatio rate agreement (uniformDerivativeOrder δ) (uniformMultiplicity δ) := by
    simpa only [uniformMultiplicity] using hfinite
  exact hgamma'.trans hfinite'

/-- Choose an interpolation envelope from a multiplicity, size bound, and finite-ratio bounds. -/
theorem exists_ratePartitionEnvelope {δ : ℝ} {m n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (hmorder : uniformDerivativeOrder δ + 2 ≤ m)
    (hsize : (m : ℝ) ≤ δ ^ 2 * n)
    (hlow : (151 / 150 : ℝ) < partitionFiniteRatio (2 * δ ^ 2) δ
      (uniformDerivativeOrder δ) m)
    (hhigh : ∀ R, δ ^ 2 ≤ R → R ≤ 1 - δ →
      (151 / 150 : ℝ) < partitionFiniteRatio R (R + δ) (uniformDerivativeOrder δ) m) :
    Nonempty (RatePartitionEnvelope δ m n k A) := by
  have hδone : δ < 1 := by linarith
  have hm : 0 < m := by omega
  have hkA : k ≤ A := by
    have : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast this
  have hnpos : 0 < n := hk.trans_le (hkA.trans hAn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  by_cases hhighRate : δ ^ 2 * n ≤ k
  · let R : ℝ := (k : ℝ) / n
    let a : ℝ := R + δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [a]; linarith
    have hRlow : δ ^ 2 ≤ R := by
      dsimp [R]
      exact (le_div_iff₀ hnR).2 (by simpa only [Nat.cast_ofNat] using hhighRate)
    have hRtop : R ≤ 1 - δ := by
      dsimp [R]
      apply (div_le_iff₀ hnR).2
      have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
      nlinarith
    obtain ⟨horder, hambient⟩ := high_rate_ambient_guards hδ.le hmorder hsize
      hhighRate hgap hAn
    have hrateUpper : (k : ℝ) ≤ R * n := by
      dsimp [R]
      field_simp
      exact le_rfl
    have hagreementLower : a * n ≤ A := by
      calc
        a * n = (k : ℝ) + δ * n := by dsimp [a, R]; field_simp
        _ ≤ A := hgap
    refine ⟨⟨k, R, a, hRpos, hRa, ?_, horder, hambient, Nat.le_succ k,
      hhighRate, hrateUpper, hagreementLower, ?_⟩⟩
    · dsimp [a]
      linarith
    · exact hhigh R hRlow hRtop
  · let D : ℕ := ⌊2 * δ ^ 2 * n⌋₊
    let R : ℝ := 2 * δ ^ 2
    let a : ℝ := δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [R, a]; nlinarith
    obtain ⟨horder, hDlower, hambient⟩ :=
      low_rate_padded_ambient_guards hδ.le (by linarith) hmorder hsize
    have hkDreal : (k : ℝ) ≤ D := by
      have hklt : (k : ℝ) < δ ^ 2 * n := lt_of_not_ge hhighRate
      exact hklt.le.trans (by exact_mod_cast hDlower)
    have hkD : k ≤ D := by exact_mod_cast hkDreal
    have hrateUpper : (D : ℝ) ≤ R * n := by
      dsimp [D, R]
      exact Nat.floor_le (by positivity)
    have hagreementLower : a * n ≤ A := by
      dsimp [a]
      nlinarith [Nat.cast_nonneg k (α := ℝ)]
    refine ⟨⟨D, R, a, hRpos, hRa, hδone.le, horder, hambient,
      hkD.trans (Nat.le_succ D), hDlower, hrateUpper, hagreementLower, hlow⟩⟩

/-- The executable multiplicity supplies the bounds for the shared rate-partition envelope. -/
theorem exists_uniformRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformBlockThreshold δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (RatePartitionEnvelope δ (uniformMultiplicity δ) n k A) := by
  have hδone : δ < 1 := by linarith
  have hd500 : 500 ≤ uniformDerivativeOrder δ :=
    (by norm_num : 500 ≤ 519).trans (uniformDerivativeOrder_ge_519 hδ hδsmall)
  have hmorder : uniformDerivativeOrder δ + 2 ≤ uniformMultiplicity δ :=
    add_two_le_uniformMultiplicity δ
  obtain ⟨hsize', _hmn, _hν, _hνn⟩ :=
    uniformBlockThreshold_guards hδ hδone.le hn
  have hsize : (uniformMultiplicity δ : ℝ) ≤ δ ^ 2 * n := by linarith
  have hRpos : 0 < 2 * δ ^ 2 := by positivity
  have hRa : 2 * δ ^ 2 ≤ δ := by nlinarith
  have hlow := finiteRatio_gt_of_uniformRateGamma hd500 hRpos hRa
    (uniformRateGamma_low_gt hδ hδsmall)
  have hhigh : ∀ R, δ ^ 2 ≤ R → R ≤ 1 - δ →
      (151 / 150 : ℝ) <
        partitionFiniteRatio R (R + δ) (uniformDerivativeOrder δ)
          (uniformMultiplicity δ) := by
    intro R hRlow hRtop
    have hRpos : 0 < R := (sq_pos_of_pos hδ).trans_le hRlow
    have hRa : R ≤ R + δ := by linarith
    exact finiteRatio_gt_of_uniformRateGamma hd500 hRpos hRa
      (uniformRateGamma_high_gt hδ hδsmall hRlow hRtop)
  exact exists_ratePartitionEnvelope hδ hδsmall hk hgap hAn hmorder hsize hlow hhigh

/-- The uniform envelope and block threshold give the common numerical and characteristic
guards needed by exact-agreement certificate endpoints. -/
theorem uniformEnvelope_exactAgreementGuards {F : Type*} [Semiring F]
    {δ : ℝ} {n k A : ℕ}
    (e : RatePartitionEnvelope δ (uniformMultiplicity δ) n k A)
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformBlockThreshold δ ≤ n) (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    500 ≤ uniformDerivativeOrder δ ∧ δ < 1 ∧ 0 < uniformJetCap δ ∧
      uniformJetCap δ < n ∧ 1 < 1000 * (uniformDerivativeOrder δ : ℝ) ^ 3 ∧ k ≤ A ∧
      (ringChar F = 0 ∨
        max (e.ambientDegree + 1 - 1) (uniformJetCap δ) < ringChar F) := by
  have hd := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hd500 : 500 ≤ uniformDerivativeOrder δ :=
    (by norm_num : 500 ≤ 519).trans hd
  have hδone : δ < 1 := by linarith
  obtain ⟨_, _, hν, hνn⟩ := uniformBlockThreshold_guards hδ hδone.le hn
  have hscale : (1 : ℝ) < 1000 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    have hd' : (500 : ℝ) ≤ uniformDerivativeOrder δ := by exact_mod_cast hd500
    nlinarith [sq_nonneg (uniformDerivativeOrder δ : ℝ)]
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg n)]
    exact_mod_cast h
  have hchar' : ringChar F = 0 ∨
      max (e.ambientDegree + 1 - 1) (uniformJetCap δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hambient_le := e.ambient_le
    have hambient : e.ambientDegree + 1 - 1 < n := by omega
    exact (max_lt hambient hνn).trans_le hc
  exact ⟨hd500, hδone, hν, hνn, hscale, hkA, hchar'⟩

end ReedSolomon.HiddenDerivative.RatePartition
