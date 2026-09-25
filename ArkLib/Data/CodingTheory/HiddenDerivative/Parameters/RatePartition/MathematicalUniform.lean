/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformEnvelope
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformGamma
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateBound

/-!
# The 300-based uniform rate-partition parameters

For small gaps, order `⌈exp(3/(2δ))⌉₊` and scale-300 multiplicity give a strict jet cap, a
uniform finite-ratio margin in both rate branches, and an envelope for the actual message
dimension and agreement.

## Main statements

* `uniformMathematicalMultiplicity`, `uniformMathematicalJetBound`, and
  `uniformMathematicalLength`.
* `uniformDerivativeOrder_le_mathematicalJetBound` and `uniformMathematical_integer_guards`.
* `uniformMathematical_totalJetDegree_le`, `uniformMathematical_low_ratio_gt`, and
  `uniformMathematical_high_ratio_gt`.
* `exists_mathematicalRatePartitionEnvelope`, a specialization of `exists_ratePartitionEnvelope`.
* `uniformMathematicalCapacityLength`, the length threshold combining the mathematical length with
  the Johnson length `⌈4 ν / δ²⌉₊` at the jet cap `ν`.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

open PolynomialDifferential

/-- The multiplicity at scale `300` for the uniform derivative order. -/
def uniformMathematicalMultiplicity (δ : ℝ) : ℕ :=
  closedMultiplicity 300 (uniformDerivativeOrder δ)

/-- The strict total-jet cap at the uniform mathematical multiplicity. -/
def uniformMathematicalJetBound (δ : ℝ) : ℕ :=
  ⌈(uniformMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1

/-- The mathematical block-length threshold, one more than the strict jet cap. -/
def uniformMathematicalLength (δ : ℝ) : ℕ :=
  uniformMathematicalJetBound δ + 1

/-- When the multiplicity is positive, the mathematical length is its rounded gap ratio. -/
theorem uniformMathematicalLength_eq_ceil {δ : ℝ}
    (hδ : 0 < δ) (hm : 0 < uniformMathematicalMultiplicity δ) :
    uniformMathematicalLength δ =
      ⌈(uniformMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ := by
  have hceil : 0 <
      ⌈(uniformMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ := by
    apply Nat.lt_ceil.mpr
    simpa only [Nat.cast_zero] using
      (div_pos (by exact_mod_cast hm :
        (0 : ℝ) < uniformMathematicalMultiplicity δ) (sq_pos_of_pos hδ))
  unfold uniformMathematicalLength uniformMathematicalJetBound
  omega

/-- The scale-300 multiplicity bounds the uniform derivative order by the jet cap. -/
theorem uniformDerivativeOrder_le_mathematicalJetBound {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25) :
    uniformDerivativeOrder δ ≤ uniformMathematicalJetBound δ := by
  have hd := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hdm : uniformDerivativeOrder δ + 2 ≤ uniformMathematicalMultiplicity δ := by
    exact (add_two_le_closedMultiplicity (by norm_num)
      (by omega : 1 ≤ uniformDerivativeOrder δ))
  have hmceil : uniformMathematicalMultiplicity δ ≤
      ⌈(uniformMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ := by
    have hδsq : δ ^ 2 ≤ 1 := by nlinarith
    have hle : (uniformMathematicalMultiplicity δ : ℝ) ≤
        (uniformMathematicalMultiplicity δ : ℝ) / δ ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hδ)).2
        (mul_le_of_le_one_right (Nat.cast_nonneg _) hδsq)
    exact_mod_cast hle.trans (Nat.le_ceil _)
  change uniformDerivativeOrder δ ≤
    ⌈(uniformMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1
  change uniformDerivativeOrder δ + 2 ≤ uniformMathematicalMultiplicity δ at hdm
  omega

/-- Length at least the mathematical threshold gives a positive multiplicity, a jet cap below
the length, and a multiplicity bounded by both the length and `δ² n`. -/
theorem uniformMathematical_integer_guards {δ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδone : δ < 1)
    (hm : 0 < uniformMathematicalMultiplicity δ)
    (hn : uniformMathematicalLength δ ≤ n) :
    let m := uniformMathematicalMultiplicity δ
    let ν := uniformMathematicalJetBound δ
    (m : ℝ) ≤ δ ^ 2 * n ∧ m ≤ n ∧ 0 < ν ∧ ν < n := by
  let m := uniformMathematicalMultiplicity δ
  let c := ⌈(m : ℝ) / δ ^ 2⌉₊
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδ2one : δ ^ 2 < 1 := by nlinarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 1 < c := by
    apply Nat.lt_ceil.mpr
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    apply (lt_div_iff₀ hδ2).mpr
    norm_num
    linarith
  have hlength : uniformMathematicalLength δ = c := by
    change c - 1 + 1 = c
    omega
  have hcn : c ≤ n := by simpa only [hlength] using hn
  have hbound : (m : ℝ) / δ ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hcn)
  have hsize : (m : ℝ) ≤ δ ^ 2 * n := by
    simpa only [mul_comm] using (div_le_iff₀ hδ2).mp hbound
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  exact ⟨hsize, hmn, by change 0 < c - 1; omega, by change c - 1 < n; omega⟩

/-- Eligible partition exponents have total jet degree at most the uniform mathematical cap. -/
theorem uniformMathematical_totalJetDegree_le {D d W n A : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D)
    (hDlower : δ ^ 2 * n ≤ D) (hAn : A ≤ n)
    {u : JetVariable d →₀ ℕ}
    (hu : PartitionSupportEligible D d W
      (uniformMathematicalMultiplicity δ * A : ℕ) u) :
    totalJetDegree u ≤ uniformMathematicalJetBound δ := by
  simpa only [uniformMathematicalJetBound] using
    partitionSupport_totalJetDegree_le_of_ambient_lower_bound hD hδ hDlower hAn hu

private theorem mathematical_uniform_margin_numeric :
    (151 / 150 : ℝ) < Real.exp (3 / 2 - Real.log (40 / 9)) *
      Real.exp (-(1677 / 1000000 : ℝ)) := by
  have hlog151 : Real.log (151 / 150 : ℝ) < 1 / 150 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 151 / 150)
      (by norm_num : (151 / 150 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hlog := log_forty_ninths_lt_d9
  have hexponent : Real.log (151 / 150 : ℝ) <
      3 / 2 - Real.log (40 / 9) - 1677 / 1000000 := by
    linarith
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 151 / 150), ← Real.exp_add]
  exact Real.exp_lt_exp.mpr hexponent

private theorem finiteRatio_gt_of_mathematicalBase {δ rate agreement : ℝ}
    (horder : 500 ≤ uniformDerivativeOrder δ) (hrate : 0 < rate)
    (hra : rate ≤ agreement)
    (hbase : Real.exp (3 / 2 - Real.log (40 / 9)) <
      rateGamma rate agreement (uniformDerivativeOrder δ)) :
    (151 / 150 : ℝ) < partitionFiniteRatio rate agreement
      (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ) := by
  have hd : 0 < uniformDerivativeOrder δ := by omega
  have hd' : (500 : ℝ) ≤ uniformDerivativeOrder δ := by exact_mod_cast horder
  have hscale : (1 : ℝ) < 300 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (uniformDerivativeOrder δ : ℝ)]
  have hloss := closedMultiplicityLoss_three_hundred_lt horder
  have hfinite := partitionFiniteRatio_closedMultiplicity_gt
    (rate := rate) (agreement := agreement) (scale := 300)
    (η := 1677 / 1000000) (order := uniformDerivativeOrder δ)
    hrate hra hscale hloss
  have hgamma := mathematical_uniform_margin_numeric.trans
    (mul_lt_mul_of_pos_right hbase (Real.exp_pos (-(1677 / 1000000 : ℝ))))
  have hgamma' : (151 / 150 : ℝ) <
      (27 / 20 : ℝ) * rate * (uniformDerivativeOrder δ + 1) *
        Real.exp (-(rate / agreement *
          Real.log (6 * (uniformDerivativeOrder δ : ℝ)))) *
        Real.exp (-(1677 / 1000000 : ℝ)) := by
    simpa only [rateGamma_eq_exponential (rate := rate) (agreement := agreement) hd]
      using hgamma
  have hfinite' :
      (27 / 20 : ℝ) * rate * (uniformDerivativeOrder δ + 1) *
          Real.exp (-(rate / agreement *
            Real.log (6 * (uniformDerivativeOrder δ : ℝ)))) *
          Real.exp (-(1677 / 1000000 : ℝ)) <
        partitionFiniteRatio rate agreement (uniformDerivativeOrder δ)
          (uniformMathematicalMultiplicity δ) := by
    simpa only [uniformMathematicalMultiplicity] using hfinite
  exact hgamma'.trans hfinite'

/-- The low-rate branch retains a strict finite-ratio margin at scale `300`. -/
theorem uniformMathematical_low_ratio_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (151 / 150 : ℝ) < partitionFiniteRatio (2 * δ ^ 2) δ
      (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ) := by
  have horder : 500 ≤ uniformDerivativeOrder δ := by
    have h := uniformDerivativeOrder_ge_519 hδ hδmax
    omega
  exact finiteRatio_gt_of_mathematicalBase horder (by positivity) (by nlinarith)
    (uniformRateGamma_low_base_gt hδ hδmax)

/-- The high-rate branch retains a strict finite-ratio margin at scale `300`. -/
theorem uniformMathematical_high_ratio_gt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    (151 / 150 : ℝ) < partitionFiniteRatio R (R + δ)
      (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ) := by
  have horder : 500 ≤ uniformDerivativeOrder δ := by
    have h := uniformDerivativeOrder_ge_519 hδ hδmax
    omega
  exact finiteRatio_gt_of_mathematicalBase horder
    ((sq_pos_of_pos hδ).trans_le hRlow) (by linarith)
    (uniformRateGamma_high_base_gt hδ hδmax hRlow hRtop)

/-- Choose a scale-300 mathematical envelope uniformly in the actual code rate. -/
theorem exists_mathematicalRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (RatePartitionEnvelope δ (uniformMathematicalMultiplicity δ) n k A) := by
  have hδone : δ < 1 := by linarith
  have hd519 := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hmorder : uniformDerivativeOrder δ + 2 ≤ uniformMathematicalMultiplicity δ :=
    add_two_le_closedMultiplicity (by norm_num) (by omega)
  have hm : 0 < uniformMathematicalMultiplicity δ := by omega
  obtain ⟨hsize, _hmn, _hν, _hνn⟩ :=
    uniformMathematical_integer_guards hδ hδone hm hn
  have hhigh : ∀ R, δ ^ 2 ≤ R → R ≤ 1 - δ →
      (151 / 150 : ℝ) < partitionFiniteRatio R (R + δ)
        (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ) := by
    intro R hRlow hRtop
    exact uniformMathematical_high_ratio_gt hδ hδsmall hRlow hRtop
  exact exists_ratePartitionEnvelope hδ hδsmall hk hgap hAn hmorder hsize
    (uniformMathematical_low_ratio_gt hδ hδsmall) hhigh

/-- The capacity length threshold: the mathematical length, and at least `4 ν / δ²` for the jet
cap `ν`, so that message dimensions up to the jet cap lie in the Johnson regime. -/
def uniformMathematicalCapacityLength (δ : ℝ) : ℕ :=
  max (uniformMathematicalLength δ) ⌈(4 : ℝ) * uniformMathematicalJetBound δ / δ ^ 2⌉₊

end ReedSolomon.HiddenDerivative.RatePartition
