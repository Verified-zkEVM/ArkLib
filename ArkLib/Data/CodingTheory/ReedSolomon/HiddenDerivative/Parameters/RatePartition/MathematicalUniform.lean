/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Rounding300
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.UniformEnvelope

/-!
# The revised 300-based uniform mathematical recipe

These parameters are deliberately separate from `uniformRatePartitionMultiplicity` and its
1000-based executable consumers. They provide the manuscript's mathematical envelope while the
complete reference executor retains its already-verified recipe.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

/-- Revised mathematical multiplicity at the existing three-halves derivative order. -/
def uniformRatePartitionMathematicalMultiplicity (δ : ℝ) : ℕ :=
  ratePartitionMathematicalMultiplicity (uniformRatePartitionOrder δ)

/-- Revised strict total-jet cap. -/
def uniformRatePartitionMathematicalJetBound (δ : ℝ) : ℕ :=
  ⌈(uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1

/-- Revised mathematical block threshold: exactly one more than the strict jet cap. -/
def uniformRatePartitionMathematicalLength (δ : ℝ) : ℕ :=
  uniformRatePartitionMathematicalJetBound δ + 1

/-- On the admissible branch, the manuscript's `Bjet + 1` threshold is exactly the rounded
multiplicity-to-gap ratio. -/
theorem uniformRatePartitionMathematicalLength_eq_ceil {δ : ℝ}
    (hδ : 0 < δ) (hm : 0 < uniformRatePartitionMathematicalMultiplicity δ) :
    uniformRatePartitionMathematicalLength δ =
      ⌈(uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ := by
  have hceil : 0 <
      ⌈(uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ := by
    apply Nat.lt_ceil.mpr
    simpa only [Nat.cast_zero] using
      (div_pos (by exact_mod_cast hm :
        (0 : ℝ) < uniformRatePartitionMathematicalMultiplicity δ) (sq_pos_of_pos hδ))
  unfold uniformRatePartitionMathematicalLength uniformRatePartitionMathematicalJetBound
  omega

/-- The three-halves order is at least `519` throughout the small-gap branch. -/
theorem uniformRatePartitionOrder_ge_519 {δ : ℝ} (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    519 ≤ uniformRatePartitionOrder δ := by
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
  have hceil : (518 : ℝ) < uniformRatePartitionOrder δ := by
    rw [uniformRatePartitionOrder, heq]
    exact hexp.trans_le (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The 300-based mathematical multiplicity dominates the support guards. -/
theorem ratePartitionMathematicalMultiplicity_ge_order {d : ℕ} (hd : 519 ≤ d) :
    d + 2 ≤ ratePartitionMathematicalMultiplicity d := by
  have hd' : (519 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 1 < Real.log (6 * d) :=
    (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 6 * d)).2
      (Real.exp_one_lt_three.trans (by linarith))
  have hm : 300 * (d : ℝ) ^ 2 * Real.log (6 * d) ≤
      ratePartitionMathematicalMultiplicity d := Nat.le_ceil _
  have hh := mul_le_mul_of_nonneg_left hlog.le (by positivity : 0 ≤ 300 * (d : ℝ) ^ 2)
  have h : (d : ℝ) + 2 ≤ ratePartitionMathematicalMultiplicity d := by nlinarith
  exact_mod_cast h

/-- The uniform jet bound dominates the reconstruction order. -/
theorem uniformRatePartitionOrder_le_mathematicalJetBound {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25) :
    uniformRatePartitionOrder δ ≤ uniformRatePartitionMathematicalJetBound δ := by
  have hd := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hdm := ratePartitionMathematicalMultiplicity_ge_order hd
  have hceil := Nat.le_ceil
    ((uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2)
  have hmceil : uniformRatePartitionMathematicalMultiplicity δ ≤
      ⌈(uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ := by
    have hδsq : δ ^ 2 ≤ 1 := by nlinarith
    have hle : (uniformRatePartitionMathematicalMultiplicity δ : ℝ) ≤
        (uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hδ)).2
        (mul_le_of_le_one_right (Nat.cast_nonneg _) hδsq)
    exact_mod_cast hle.trans hceil
  change uniformRatePartitionOrder δ ≤
    ⌈(uniformRatePartitionMathematicalMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1
  change uniformRatePartitionOrder δ + 2 ≤
    uniformRatePartitionMathematicalMultiplicity δ at hdm
  omega

/-- Revised length gives the finite multiplicity and characteristic guards. -/
theorem uniformRatePartitionMathematical_integer_guards {δ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδone : δ < 1)
    (hm : 0 < uniformRatePartitionMathematicalMultiplicity δ)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) :
    let m := uniformRatePartitionMathematicalMultiplicity δ
    let ν := uniformRatePartitionMathematicalJetBound δ
    (m : ℝ) ≤ δ ^ 2 * n ∧ m ≤ n ∧ 0 < ν ∧ ν < n := by
  let m := uniformRatePartitionMathematicalMultiplicity δ
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
  have hlength : uniformRatePartitionMathematicalLength δ = c := by
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

/-- Both rate branches give the revised total-jet cap. -/
theorem uniformRatePartitionMathematical_totalJetDegree_le {D d W n A : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D)
    (hDlower : δ ^ 2 * n ≤ D) (hAn : A ≤ n)
    {u : JetVariable d →₀ ℕ}
    (hu : RatePartitionEligible D d W
      (uniformRatePartitionMathematicalMultiplicity δ * A : ℕ) u) :
    totalJetDegree u ≤ uniformRatePartitionMathematicalJetBound δ := by
  let m := uniformRatePartitionMathematicalMultiplicity δ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht := totalJetDegree_lt_of_ratePartitionEligible hD hu
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
  exact Nat.le_sub_one_of_lt hlt

private theorem revised_log_forty_ninths_eq :
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

private theorem revised_uniform_margin_numeric :
    (151 / 150 : ℝ) < Real.exp (3 / 2 - Real.log (40 / 9)) *
      Real.exp (-(1677 / 1000000 : ℝ)) := by
  have hlog151 : Real.log (151 / 150 : ℝ) < 1 / 150 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 151 / 150)
      (by norm_num : (151 / 150 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hlog409 : Real.log (40 / 9 : ℝ) <
      3 * (0.6931471808 : ℝ) + 1.6094379126 - 2 * 1.0986122885 := by
    rw [revised_log_forty_ninths_eq]
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

/-- Revised low-rate finite-ratio margin at the 300-based multiplicity. -/
theorem uniformRatePartitionMathematical_low_ratio_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (151 / 150 : ℝ) < ratePartitionFiniteRatio (2 * δ ^ 2) δ
      (uniformRatePartitionOrder δ) (uniformRatePartitionMathematicalMultiplicity δ) := by
  have hd := uniformRatePartitionOrder_ge_519 hδ hδmax
  have hR : 0 < 2 * δ ^ 2 := by positivity
  have hRa : 2 * δ ^ 2 < δ := by nlinarith
  have hbase := uniformRatePartitionGamma_low_base_gt hδ hδmax
  have hfinite := ratePartition_mathematical_ratio_gt hR hRa hd
  have hfinite' :
      ratePartitionGamma (2 * δ ^ 2) δ (uniformRatePartitionOrder δ) *
          Real.exp (-(1677 / 1000000 : ℝ)) <
        ratePartitionFiniteRatio (2 * δ ^ 2) δ (uniformRatePartitionOrder δ)
          (uniformRatePartitionMathematicalMultiplicity δ) := by
    simpa only [uniformRatePartitionMathematicalMultiplicity] using
      (show ratePartitionGamma (2 * δ ^ 2) δ (uniformRatePartitionOrder δ) *
          Real.exp (-(1677 / 1000000 : ℝ)) < _ from hfinite)
  exact revised_uniform_margin_numeric.trans <|
    (mul_lt_mul_of_pos_right hbase
      (Real.exp_pos (-(1677 / 1000000 : ℝ)))).trans hfinite'

/-- Revised high-rate finite-ratio margin at the 300-based multiplicity. -/
theorem uniformRatePartitionMathematical_high_ratio_gt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    (151 / 150 : ℝ) < ratePartitionFiniteRatio R (R + δ)
      (uniformRatePartitionOrder δ) (uniformRatePartitionMathematicalMultiplicity δ) := by
  have hd := uniformRatePartitionOrder_ge_519 hδ hδmax
  have hR : 0 < R := (sq_pos_of_pos hδ).trans_le hRlow
  have hRa : R < R + δ := by linarith
  have hbase := uniformRatePartitionGamma_high_base_gt hδ hδmax hRlow hRtop
  have hfinite := ratePartition_mathematical_ratio_gt hR hRa hd
  have hfinite' :
      ratePartitionGamma R (R + δ) (uniformRatePartitionOrder δ) *
          Real.exp (-(1677 / 1000000 : ℝ)) <
        ratePartitionFiniteRatio R (R + δ) (uniformRatePartitionOrder δ)
          (uniformRatePartitionMathematicalMultiplicity δ) := by
    simpa only [uniformRatePartitionMathematicalMultiplicity] using
      (show ratePartitionGamma R (R + δ) (uniformRatePartitionOrder δ) *
          Real.exp (-(1677 / 1000000 : ℝ)) < _ from hfinite)
  exact revised_uniform_margin_numeric.trans <|
    (mul_lt_mul_of_pos_right hbase
      (Real.exp_pos (-(1677 / 1000000 : ℝ)))).trans hfinite'

/-- A rate-uniform mathematical envelope using the revised multiplicity. -/
structure MathematicalRatePartitionEnvelope (δ : ℝ) (n k A : ℕ) where
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
    (uniformRatePartitionOrder δ) (uniformRatePartitionMathematicalMultiplicity δ)

/-- Choose the revised mathematical envelope uniformly in the actual code rate. -/
theorem exists_mathematicalRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (MathematicalRatePartitionEnvelope δ n k A) := by
  have hδone : δ < 1 := by linarith
  have hd519 := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hmorder := ratePartitionMathematicalMultiplicity_ge_order hd519
  have hm : 0 < uniformRatePartitionMathematicalMultiplicity δ := by
    exact lt_of_lt_of_le (by omega) hmorder
  obtain ⟨hsize, _hmn, _hν, _hνn⟩ :=
    uniformRatePartitionMathematical_integer_guards hδ hδone hm hn
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
    obtain ⟨horder, hambient⟩ := uniformRatePartition_high_ambient_of_m_le
      hδ hδone hmorder hsize hhigh hgap hAn
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
    · exact uniformRatePartitionMathematical_high_ratio_gt hδ hδsmall hRlow hRtop
  · let D : ℕ := ⌊2 * δ ^ 2 * n⌋₊
    let R : ℝ := 2 * δ ^ 2
    let a : ℝ := δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRa : R < a := by dsimp [R, a]; nlinarith
    obtain ⟨horder, hDlower, hambient⟩ := uniformRatePartition_low_ambient_of_m_le
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
    refine ⟨⟨D, R, a, hRpos, hRa, hδone.le, horder, hambient,
      hkD.trans (Nat.le_succ D), hDlower, hrateUpper, hagreementLower, ?_⟩⟩
    exact uniformRatePartitionMathematical_low_ratio_gt hδ hδsmall

end ReedSolomon.HiddenDerivative
