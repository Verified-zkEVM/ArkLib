/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.Counting
public import ArkLib.ToMathlib.Combinatorics.QuadraticStaircase

/-!
# Quadratic source lower bound

Fixing the derivative tuple leaves two source exponents, `X` and `Y₀`.
Their staircase count dominates the corresponding triangular area. Summing over
the derivative tuples gives the positive-part square needed by the simplex moment,
without discarding tuples near the specialization boundary.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- The real staircase cutoff gives exactly the integer residual count at each zeroth jet. -/
theorem partition_residual_ceil {D budget degree : ℕ} (hD : 0 < D) (zeroth : ℕ) :
    ⌈(D : ℝ) * ((budget : ℝ) / D - degree - zeroth)⌉₊ =
      budget - D * (zeroth + degree) := by
  have hDzero : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hequal : (D : ℝ) * ((budget : ℝ) / D - degree - zeroth) =
      (budget : ℝ) - (D * (zeroth + degree) : ℕ) := by
    push_cast
    field_simp
    ring
  rw [hequal, Nat.ceil_sub_natCast, Nat.ceil_natCast]

/-- The finite source slice includes the entire quadratic staircase. -/
theorem quadraticStaircase_le_partition_slice {D budget degree : ℕ} (hD : 0 < D) :
    QuadraticStaircase.count D ((budget : ℝ) / D - degree) ≤
      ∑ zeroth ∈ Finset.range budget, (budget - D * (zeroth + degree)) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hDOne : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hceil : ⌈(budget : ℝ) / D - degree⌉₊ ≤ budget := by
    apply Nat.ceil_le.mpr
    have hquot : (budget : ℝ) / D ≤ budget := by
      apply (div_le_iff₀ hDR).mpr
      nlinarith [Nat.cast_nonneg budget (α := ℝ)]
    exact (sub_le_self _ (Nat.cast_nonneg degree)).trans hquot
  unfold QuadraticStaircase.count
  simp_rw [partition_residual_ceil hD]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hceil)

/-- All derivative tuples contribute their full positive-part quadratic residual. -/
theorem partitionSupport_dimension_ge_quadratic_sum {F : Type*} [Field F]
    {D d m A W : ℕ} (hD : 0 < D) :
    (∑ jets ∈ weightedHigherJetTuples (d + 1) W,
      (D : ℝ) * (max ((m * A : ℕ) / (D : ℝ) - higherJetTupleDegree jets) 0) ^ 2 / 2) ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  rw [finrank_partitionSupportSpace_eq_sourceCount hD]
  unfold partitionSourceCount
  simp only [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro jets _
  apply (QuadraticStaircase.count_ge_quadratic D
    ((m * A : ℕ) / (D : ℝ) - higherJetTupleDegree jets)).trans
  have hcount := quadraticStaircase_le_partition_slice (budget := m * A)
    (degree := higherJetTupleDegree jets) hD
  exact_mod_cast hcount

/-- An upper rate bound and a lower agreement rate bound control each triangular source
contribution, even when the actual ambient degree is smaller than `R*n`. -/
theorem partition_quadratic_rate_lower {D n m A degree : ℕ} {rate agreement : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hrate : 0 < rate)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A) :
    (n : ℝ) / (2 * rate) * (max ((m : ℝ) * agreement - rate * degree) 0) ^ 2 ≤
      (D : ℝ) * (max ((m * A : ℕ) / (D : ℝ) - degree) 0) ^ 2 / 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsource : (n : ℝ) * ((m : ℝ) * agreement - rate * degree) ≤
      (m * A : ℕ) - (D : ℝ) * degree := by
    have hagreement := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hdegree := mul_le_mul_of_nonneg_right hupper
      (Nat.cast_nonneg degree : (0 : ℝ) ≤ degree)
    push_cast
    nlinarith
  have hmax : (n : ℝ) * max ((m : ℝ) * agreement - rate * degree) 0 ≤
      max ((m * A : ℕ) - (D : ℝ) * degree) 0 := by
    rw [mul_max_of_nonneg _ _ hnR.le, mul_zero]
    exact max_le_max_right 0 hsource
  have hquot : ((n : ℝ) * max ((m : ℝ) * agreement - rate * degree) 0) ^ 2 /
      (2 * rate * n) ≤
      (max ((m * A : ℕ) - (D : ℝ) * degree) 0) ^ 2 / (2 * D) := by
    apply div_le_div₀ (by positivity)
    · exact pow_le_pow_left₀ (by positivity) hmax 2
    · positivity
    · nlinarith
  have hleft : ((n : ℝ) * max ((m : ℝ) * agreement - rate * degree) 0) ^ 2 /
      (2 * rate * n) =
      (n : ℝ) / (2 * rate) * (max ((m : ℝ) * agreement - rate * degree) 0) ^ 2 := by
    field_simp
  have hright : (max ((m * A : ℕ) - (D : ℝ) * degree) 0) ^ 2 / (2 * D) =
      (D : ℝ) * (max ((m * A : ℕ) / (D : ℝ) - degree) 0) ^ 2 / 2 := by
    have hfactor : (m * A : ℕ) - (D : ℝ) * degree =
        D * ((m * A : ℕ) / (D : ℝ) - degree) := by field_simp
    have hmaxfactor := mul_max_of_nonneg
      ((m * A : ℕ) / (D : ℝ) - degree) 0 hDR.le
    simp only [mul_zero] at hmaxfactor
    rw [hfactor, ← hmaxfactor, mul_pow]
    field_simp
  simpa only [hleft, hright] using hquot

/-- The finite source sum has the rate-dependent positive-part-square lower bound. -/
theorem partitionSupport_dimension_ge_rate_sum {F : Type*} [Field F]
    {D d n m A W : ℕ} {rate agreement : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hrate : 0 < rate)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A) :
    (n : ℝ) / (2 * rate) *
      (∑ jets ∈ weightedHigherJetTuples (d + 1) W,
        (max ((m : ℝ) * agreement - rate * higherJetTupleDegree jets) 0) ^ 2) ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  rw [Finset.mul_sum]
  apply le_trans _ (partitionSupport_dimension_ge_quadratic_sum hD)
  apply Finset.sum_le_sum
  intro jets _
  exact partition_quadratic_rate_lower hD hn hrate hupper hlower

end ReedSolomon.HiddenDerivative
