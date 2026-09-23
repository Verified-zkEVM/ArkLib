/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformGamma

/-!
# The 300-based uniform rate-partition parameters

For small gaps, order `⌈exp(3/(2δ))⌉₊` and scale-300 multiplicity give a strict jet cap, a
uniform finite-ratio margin in both rate branches, and an envelope for the actual message
dimension and agreement.

## Main statements

* `uniformMathematicalMultiplicity`, `uniformMathematicalJetBound`,
  `uniformMathematicalLength`, and `uniformCapacityLengthThreshold300`.
* `uniformDerivativeOrder_ge_519`, `uniformDerivativeOrder_le_mathematicalJetBound`, and
  `uniformMathematical_integer_guards`.
* `uniformMathematical_totalJetDegree_le`, `uniformMathematical_low_ratio_gt`, and
  `uniformMathematical_high_ratio_gt`.
* `MathematicalRatePartitionEnvelope` and `exists_mathematicalRatePartitionEnvelope`.

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

/-- A common length threshold for interpolation and the characteristic-free Johnson regime. -/
def uniformCapacityLengthThreshold300 (δ : ℝ) : ℕ :=
  max (uniformMathematicalLength δ)
    ⌈(4 : ℝ) * uniformMathematicalJetBound δ / δ ^ 2⌉₊

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

/-- The uniform derivative order is at least `519` for `0 < δ < 6/25`. -/
theorem uniformDerivativeOrder_ge_519 {δ : ℝ} (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    519 ≤ uniformDerivativeOrder δ := by
  have hexponent : (25 / 4 : ℝ) < 3 / (2 * δ) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hδ)).2
    nlinarith
  have hseries := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 25 / 4 by norm_num) 20
  have h518 : (518 : ℝ) < Real.exp (25 / 4) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    exact lt_of_lt_of_le (by norm_num) hseries
  have hexp : (518 : ℝ) < Real.exp (3 / (2 * δ)) :=
    h518.trans (Real.exp_lt_exp.mpr hexponent)
  have heq : (3 / 2 : ℝ) / δ = 3 / (2 * δ) := by field_simp
  have hceil : (518 : ℝ) < uniformDerivativeOrder δ := by
    rw [uniformDerivativeOrder, heq]
    exact hexp.trans_le (Nat.le_ceil _)
  exact_mod_cast hceil

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
  let m := uniformMathematicalMultiplicity δ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht := totalJetDegree_lt_of_partitionSupportEligible hD hu
  have hb : ((m * A : ℕ) : ℝ) / D ≤ (m : ℝ) / δ ^ 2 := by
    apply (div_le_div_iff₀ hD' hδ2).2
    have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hDlower hm',
      mul_le_mul_of_nonneg_left hAn' (mul_nonneg hm' hδ2.le)]
  have hc : (m : ℝ) / δ ^ 2 ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ := Nat.le_ceil _
  have hlt : totalJetDegree u < ⌈(m : ℝ) / δ ^ 2⌉₊ := by
    exact_mod_cast (ht.trans_le (hb.trans hc))
  change totalJetDegree u ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ - 1
  exact Nat.le_sub_one_of_lt hlt

private theorem mathematical_log_forty_ninths_eq :
    Real.log (40 / 9 : ℝ) =
      3 * Real.log 2 + Real.log 5 - 2 * Real.log 3 := by
  calc
    Real.log (40 / 9 : ℝ) = Real.log 40 - Real.log 9 := by
      rw [Real.log_div] <;> norm_num
    _ = 3 * Real.log 2 + Real.log 5 - 2 * Real.log 3 := by
      rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num,
        show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_mul] <;> try positivity
      rw [Real.log_pow, Real.log_pow]
      norm_num

private theorem mathematical_uniform_margin_numeric :
    (151 / 150 : ℝ) < Real.exp (3 / 2 - Real.log (40 / 9)) *
      Real.exp (-(1677 / 1000000 : ℝ)) := by
  have hlog151 : Real.log (151 / 150 : ℝ) < 1 / 150 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 151 / 150)
      (by norm_num : (151 / 150 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hlog409 : Real.log (40 / 9 : ℝ) <
      3 * (0.6931471808 : ℝ) + 1.6094379126 - 2 * 1.0986122885 := by
    rw [mathematical_log_forty_ninths_eq]
    have htwo := Real.log_two_lt_d9
    have hthree := Real.log_three_gt_d9
    have hfive := Real.log_five_lt_d9
    norm_num at htwo hthree hfive ⊢
    have htwo3 := mul_lt_mul_of_pos_left htwo (by norm_num : (0 : ℝ) < 3)
    have hthree2 := mul_lt_mul_of_neg_left hthree (by norm_num : (-2 : ℝ) < 0)
    calc
      3 * Real.log 2 + Real.log 5 - 2 * Real.log 3 <
          3 * (108304247 / 156250000 : ℝ) + Real.log 5 - 2 * Real.log 3 := by
        linarith
      _ < 3 * (108304247 / 156250000 : ℝ) +
          8047189563 / 5000000000 - 2 * Real.log 3 := by linarith
      _ < 3 * (108304247 / 156250000 : ℝ) +
          8047189563 / 5000000000 - 2 * (2197224577 / 2000000000) := by
        linarith
      _ = 745827439 / 500000000 := by norm_num
  have hexponent : Real.log (151 / 150 : ℝ) <
      3 / 2 - Real.log (40 / 9) - 1677 / 1000000 := by
    linarith
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 151 / 150), ← Real.exp_add]
  exact Real.exp_lt_exp.mpr (by linarith)

private theorem rateGamma_eq_exp {rate agreement : ℝ} {order : ℕ}
    (horder : 0 < order) :
    rateGamma rate agreement order =
      (27 / 20 : ℝ) * rate * (order + 1) *
        Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) := by
  unfold rateGamma
  rw [Real.rpow_def_of_pos (by positivity : 0 < (6 * (order : ℝ) : ℝ))]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- The low-rate branch retains a strict finite-ratio margin at scale `300`. -/
theorem uniformMathematical_low_ratio_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (151 / 150 : ℝ) < partitionFiniteRatio (2 * δ ^ 2) δ
      (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ) := by
  have hd := uniformDerivativeOrder_ge_519 hδ hδmax
  have hR : 0 < 2 * δ ^ 2 := by positivity
  have hRa : 2 * δ ^ 2 < δ := by nlinarith
  have hbase := uniformRateGamma_low_base_gt hδ hδmax
  have horder : 500 ≤ uniformDerivativeOrder δ := by omega
  have horderReal : (1 : ℝ) ≤ uniformDerivativeOrder δ := by
    exact_mod_cast (by omega : 1 ≤ uniformDerivativeOrder δ)
  have hscale : (1 : ℝ) < 300 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    have hcube : (1 : ℝ) ≤ (uniformDerivativeOrder δ : ℝ) ^ 3 := by
      have hfactor := mul_nonneg (sub_nonneg.mpr horderReal)
        (by positivity : (0 : ℝ) ≤ (uniformDerivativeOrder δ : ℝ) ^ 2 +
          uniformDerivativeOrder δ + 1)
      nlinarith
    nlinarith
  have hfinite := partitionFiniteRatio_closedMultiplicity_gt
    (rate := 2 * δ ^ 2) (agreement := δ) (scale := 300)
    (η := 1677 / 1000000) (order := uniformDerivativeOrder δ)
    hR hRa.le hscale (closedMultiplicityLoss_three_hundred_lt horder)
  have hfinite' :
      rateGamma (2 * δ ^ 2) δ (uniformDerivativeOrder δ) *
          Real.exp (-(1677 / 1000000 : ℝ)) <
        partitionFiniteRatio (2 * δ ^ 2) δ (uniformDerivativeOrder δ)
          (uniformMathematicalMultiplicity δ) := by
    rw [rateGamma_eq_exp (rate := 2 * δ ^ 2) (agreement := δ) (by omega)]
    simpa only [uniformMathematicalMultiplicity] using hfinite
  exact mathematical_uniform_margin_numeric.trans <|
    (mul_lt_mul_of_pos_right hbase
      (Real.exp_pos (-(1677 / 1000000 : ℝ)))).trans hfinite'

/-- The high-rate branch retains a strict finite-ratio margin at scale `300`. -/
theorem uniformMathematical_high_ratio_gt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    (151 / 150 : ℝ) < partitionFiniteRatio R (R + δ)
      (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ) := by
  have hd := uniformDerivativeOrder_ge_519 hδ hδmax
  have hR : 0 < R := (sq_pos_of_pos hδ).trans_le hRlow
  have hRa : R < R + δ := by linarith
  have hbase := uniformRateGamma_high_base_gt hδ hδmax hRlow hRtop
  have horder : 500 ≤ uniformDerivativeOrder δ := by omega
  have horderReal : (1 : ℝ) ≤ uniformDerivativeOrder δ := by
    exact_mod_cast (by omega : 1 ≤ uniformDerivativeOrder δ)
  have hscale : (1 : ℝ) < 300 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    have hcube : (1 : ℝ) ≤ (uniformDerivativeOrder δ : ℝ) ^ 3 := by
      have hfactor := mul_nonneg (sub_nonneg.mpr horderReal)
        (by positivity : (0 : ℝ) ≤ (uniformDerivativeOrder δ : ℝ) ^ 2 +
          uniformDerivativeOrder δ + 1)
      nlinarith
    nlinarith
  have hfinite := partitionFiniteRatio_closedMultiplicity_gt
    (rate := R) (agreement := R + δ) (scale := 300)
    (η := 1677 / 1000000) (order := uniformDerivativeOrder δ)
    hR hRa.le hscale (closedMultiplicityLoss_three_hundred_lt horder)
  have hfinite' :
      rateGamma R (R + δ) (uniformDerivativeOrder δ) *
          Real.exp (-(1677 / 1000000 : ℝ)) <
        partitionFiniteRatio R (R + δ) (uniformDerivativeOrder δ)
          (uniformMathematicalMultiplicity δ) := by
    rw [rateGamma_eq_exp (rate := R) (agreement := R + δ) (by omega)]
    simpa only [uniformMathematicalMultiplicity] using hfinite
  exact mathematical_uniform_margin_numeric.trans <|
    (mul_lt_mul_of_pos_right hbase
      (Real.exp_pos (-(1677 / 1000000 : ℝ)))).trans hfinite'

/-- A rate-uniform interpolation envelope at the scale-300 mathematical multiplicity. -/
structure MathematicalRatePartitionEnvelope (δ : ℝ) (n k A : ℕ) where
  /-- The interpolation ambient degree. -/
  ambientDegree : ℕ
  /-- The scalar code rate used in the finite-ratio bound. -/
  rate : ℝ
  /-- The agreement fraction used in the finite-ratio bound. -/
  agreement : ℝ
  /-- The selected rate is positive. -/
  rate_pos : 0 < rate
  /-- The selected rate is strictly below the agreement fraction. -/
  rate_lt_agreement : rate < agreement
  /-- The agreement fraction is at most one. -/
  agreement_le_one : agreement ≤ 1
  /-- The ambient degree includes the derivative order. -/
  order_le : uniformDerivativeOrder δ + 1 ≤ ambientDegree
  /-- The ambient degree fits in the block length. -/
  ambient_le : ambientDegree + 1 ≤ n
  /-- The message dimension fits in the ambient degree. -/
  message_le : k ≤ ambientDegree + 1
  /-- The ambient degree is at least the quadratic-gap threshold. -/
  ambient_lower : δ ^ 2 * n ≤ ambientDegree
  /-- The ambient degree is at most the selected rate times the block length. -/
  rate_upper : (ambientDegree : ℝ) ≤ rate * n
  /-- The agreement fraction times the block length is at most the agreement count. -/
  agreement_lower : agreement * n ≤ A
  /-- The scale-300 finite ratio exceeds `151/150`. -/
  ratio_gt : (151 / 150 : ℝ) < partitionFiniteRatio rate agreement
    (uniformDerivativeOrder δ) (uniformMathematicalMultiplicity δ)

/-- Choose a scale-300 mathematical envelope uniformly in the actual code rate. -/
theorem exists_mathematicalRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (MathematicalRatePartitionEnvelope δ n k A) := by
  have hδone : δ < 1 := by linarith
  have hd519 := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hmorder : uniformDerivativeOrder δ + 2 ≤ uniformMathematicalMultiplicity δ := by
    exact add_two_le_closedMultiplicity (by norm_num)
      (by omega : 1 ≤ uniformDerivativeOrder δ)
  have hm : 0 < uniformMathematicalMultiplicity δ := by
    exact lt_of_lt_of_le (by omega) hmorder
  obtain ⟨hsize, _hmn, _hν, _hνn⟩ :=
    uniformMathematical_integer_guards hδ hδone hm hn
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
    obtain ⟨horder, hambient⟩ := high_rate_ambient_guards hδ.le hmorder hsize
      hhigh hgap hAn
    have hrateUpper : (k : ℝ) ≤ R * n := by
      dsimp [R]
      field_simp
      exact le_rfl
    have hagreementLower : a * n ≤ A := by
      calc
        a * n = (k : ℝ) + δ * n := by dsimp [a, R]; field_simp
        _ ≤ A := hgap
    refine ⟨⟨k, R, a, hRpos, hRa, ?_, horder, hambient, Nat.le_succ k,
      hhigh, hrateUpper, hagreementLower, ?_⟩⟩
    · dsimp [a]
      linarith
    · exact uniformMathematical_high_ratio_gt hδ hδsmall hRlow hRtop
  · let D : ℕ := ⌊2 * δ ^ 2 * n⌋₊
    let R : ℝ := 2 * δ ^ 2
    let a : ℝ := δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [R, a]; nlinarith
    obtain ⟨horder, hDlower, hambient⟩ :=
      low_rate_padded_ambient_guards hδ.le (by linarith) hmorder hsize
    have hkDreal : (k : ℝ) ≤ D := by
      have hklt : (k : ℝ) < δ ^ 2 * n := lt_of_not_ge hhigh
      exact hklt.le.trans (by exact_mod_cast hDlower)
    have hkD : k ≤ D := by exact_mod_cast hkDreal
    have hrateUpper : (D : ℝ) ≤ R * n := by
      dsimp [D, R]
      exact Nat.floor_le (by positivity)
    have hagreementLower : a * n ≤ A := by
      dsimp [a]
      nlinarith [Nat.cast_nonneg k (α := ℝ)]
    refine ⟨⟨D, R, a, hRpos, hRa, by linarith, horder, hambient,
      hkD.trans (Nat.le_succ D), hDlower, hrateUpper, hagreementLower, ?_⟩⟩
    exact uniformMathematical_low_ratio_gt hδ hδsmall

end ReedSolomon.HiddenDerivative.RatePartition
