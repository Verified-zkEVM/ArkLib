/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.SupportGuards
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit integer parameters for the uniform three-halves exponent -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

/-- The uniform derivative order in the small-gap branch. -/
def uniformRatePartitionOrder (δ : ℝ) : ℕ := ⌈Real.exp ((3 / 2) / δ)⌉₊

/-- Closed multiplicity for the uniform derivative order. -/
def uniformRatePartitionMultiplicity (δ : ℝ) : ℕ :=
  ratePartitionClosedMultiplicity (uniformRatePartitionOrder δ)

/-- Uniform block threshold, independent of the actual code rate. -/
def uniformRatePartitionLength (δ : ℝ) : ℕ :=
  ⌈2 * (uniformRatePartitionMultiplicity δ : ℝ) / δ ^ 2⌉₊

/-- The strict support inequality permits subtracting one from the rounded total-jet cap. -/
def uniformRatePartitionJetBound (δ : ℝ) : ℕ :=
  ⌈(uniformRatePartitionMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1

/-- Closed multiplicity dominates the ambient-degree guards. -/
theorem ratePartitionClosedMultiplicity_ge_order {d : ℕ} (hd : 500 ≤ d) :
    d + 2 ≤ ratePartitionClosedMultiplicity d := by
  have hd' : (500 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 1 < Real.log (6 * d) :=
    (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 6 * d)).mpr
      (Real.exp_one_lt_three.trans (by linarith))
  have hm : 1000 * (d : ℝ) ^ 2 * Real.log (6 * d) ≤
      ratePartitionClosedMultiplicity d := Nat.le_ceil _
  have hh := mul_le_mul_of_nonneg_left hlog.le (by positivity : 0 ≤ 1000 * (d : ℝ) ^ 2)
  have h : (d : ℝ) + 2 ≤ ratePartitionClosedMultiplicity d := by nlinarith
  exact_mod_cast h

/-- Uniform length gives the finite multiplicity and characteristic guards. -/
theorem uniformRatePartition_integer_guards {δ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδone : δ < 1)
    (hm : 0 < uniformRatePartitionMultiplicity δ)
    (hn : uniformRatePartitionLength δ ≤ n) :
    let m := uniformRatePartitionMultiplicity δ
    let ν := uniformRatePartitionJetBound δ
    2 * (m : ℝ) ≤ δ ^ 2 * n ∧ m ≤ n ∧ 0 < ν ∧ ν < n := by
  let m := uniformRatePartitionMultiplicity δ
  let c := ⌈(m : ℝ) / δ ^ 2⌉₊
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδ2one : δ ^ 2 < 1 := by nlinarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound : 2 * (m : ℝ) / δ ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n := by
    simpa only [mul_comm] using (div_le_iff₀ hδ2).mp hbound
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hcpos : 1 < c := by
    apply Nat.lt_ceil.mpr
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    apply (lt_div_iff₀ hδ2).mpr
    norm_num
    linarith
  have hcn : c ≤ n := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ hδ2).mpr (by nlinarith)
  exact ⟨hsize, hmn, by change 0 < c - 1; omega, by change c - 1 < n; omega⟩

/-- The high-rate and padded low-rate ambient bounds both give the sharper uniform jet cap. -/
theorem uniformRatePartition_totalJetDegree_le {D d W n A : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D)
    (hDlower : δ ^ 2 * n ≤ D) (hAn : A ≤ n)
    {u : JetVariable d →₀ ℕ}
    (hu : RatePartitionEligible D d W (uniformRatePartitionMultiplicity δ * A : ℕ) u) :
    totalJetDegree u ≤ uniformRatePartitionJetBound δ := by
  let m := uniformRatePartitionMultiplicity δ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht := totalJetDegree_lt_of_ratePartitionEligible hD hu
  have hb : ((m * A : ℕ) : ℝ) / D ≤ (m : ℝ) / δ ^ 2 := by
    apply (div_le_div_iff₀ hD' hδ2).mpr
    have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hDlower hm',
      mul_le_mul_of_nonneg_left hAn' (mul_nonneg hm' hδ2.le)]
  have hc : (m : ℝ) / δ ^ 2 ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ := Nat.le_ceil _
  have hlt : totalJetDegree u < ⌈(m : ℝ) / δ ^ 2⌉₊ := by
    exact_mod_cast (ht.trans_le (hb.trans hc))
  exact Nat.le_sub_one_of_lt hlt
/-- The uniform strict ratio gives exactly the advertised integral height. -/
theorem ratePartitionHeight_uniform {ν : ℕ} (hν : 0 < ν) :
    ratePartitionHeight ν (151 / 150 : ℝ) = 150 * ν := by
  have h : (ν : ℝ) / ((151 / 150 : ℝ) - 1) = ((150 * ν : ℕ) : ℝ) := by
    push_cast
    norm_num
    ring
  unfold ratePartitionHeight
  rw [h, Nat.ceil_natCast]
  omega

/-- The high-rate branch uses the actual message degree as its interpolation ambient degree.
Only one multiplicity-sized unit of quadratic-rate room is needed: reconstruction uses its
separate dimension and does not force an additional copy of this budget. -/
theorem uniformRatePartition_high_ambient_of_m_le {δ : ℝ} {d m n k A : ℕ}
    (hδ : 0 < δ) (hδone : δ < 1) (hm : d + 2 ≤ m)
    (hsize : (m : ℝ) ≤ δ ^ 2 * n)
    (hhigh : δ ^ 2 * n ≤ k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    d + 1 ≤ k ∧ k + 1 ≤ n := by
  have hm' : (d : ℝ) + 2 ≤ m := by exact_mod_cast hm
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hδn := mul_le_mul_of_nonneg_right hδ2 hn'
  have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
  constructor
  · have : (d : ℝ) + 1 ≤ k := by nlinarith [Nat.cast_nonneg d (α := ℝ)]
    exact_mod_cast this
  · have : (k : ℝ) + 1 ≤ n := by nlinarith [Nat.cast_nonneg d (α := ℝ)]
    exact_mod_cast this

/-- Low-rate padding stays inside the block and retains the quadratic-rate lower ambient bound
from one multiplicity-sized unit of quadratic-rate room. -/
theorem uniformRatePartition_low_ambient_of_m_le {δ : ℝ} {d m n : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25) (hm : d + 2 ≤ m)
    (hsize : (m : ℝ) ≤ δ ^ 2 * n) :
    let D := ⌊2 * δ ^ 2 * n⌋₊
    d + 1 ≤ D ∧ δ ^ 2 * n ≤ D ∧ D + 1 ≤ n := by
  let D := ⌊2 * δ ^ 2 * n⌋₊
  have hm' : (d : ℝ) + 2 ≤ m := by exact_mod_cast hm
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hfloor : (D : ℝ) ≤ 2 * δ ^ 2 * n := Nat.floor_le (by positivity)
  have hfloor' : 2 * δ ^ 2 * n < (D : ℝ) + 1 := Nat.lt_floor_add_one _
  have hDlower : δ ^ 2 * n ≤ D := by nlinarith
  have hδ2 : 2 * δ ^ 2 < 1 / 2 := by nlinarith
  have hn2 : (2 : ℝ) ≤ n := by
    have h := mul_le_mul_of_nonneg_right hδ2.le hn'
    nlinarith
  refine ⟨?_, hDlower, ?_⟩
  · have : (d : ℝ) + 1 ≤ D := by nlinarith
    exact_mod_cast this
  · have h := mul_le_mul_of_nonneg_right hδ2.le hn'
    have : (D : ℝ) + 1 ≤ n := by nlinarith
    exact_mod_cast this

/-- Compatibility wrapper for the retained executor's stronger two-copy length guard. -/
theorem uniformRatePartition_high_ambient {δ : ℝ} {d m n k A : ℕ}
    (hδ : 0 < δ) (hδone : δ < 1) (hm : d + 2 ≤ m)
    (hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n)
    (hhigh : δ ^ 2 * n ≤ k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    d + 1 ≤ k ∧ k + 1 ≤ n := by
  exact uniformRatePartition_high_ambient_of_m_le hδ hδone hm (by nlinarith)
    hhigh hgap hAn

/-- Compatibility wrapper for the retained executor's stronger two-copy length guard. -/
theorem uniformRatePartition_low_ambient {δ : ℝ} {d m n : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25) (hm : d + 2 ≤ m)
    (hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n) :
    let D := ⌊2 * δ ^ 2 * n⌋₊
    d + 1 ≤ D ∧ δ ^ 2 * n ≤ D ∧ D + 1 ≤ n := by
  exact uniformRatePartition_low_ambient_of_m_le hδ hδsmall hm (by nlinarith)

end ReedSolomon.HiddenDerivative
