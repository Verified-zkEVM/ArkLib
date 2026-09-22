/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Finite geometric sums with a linear weight, and exponential tails

For `0 ≤ q < 1` in a linearly ordered field, the finite sums `∑_{j<m} q^(j+1)` and
`∑_{j<m} (j+1) q^(j+1)` are at most their infinite values `q / (1 - q)` and `q / (1 - q)^2`.
The second follows from the closed form
`(1 - q)^2 ∑_{j<m} (j+1) q^(j+1) = q - (m+1) q^(m+1) + m q^(m+2)`, valid in every commutative
ring. Combining them bounds `∑_{j<m} (a (j+1) + b) q^(j+1)` for `a, b ≥ 0`.

At `q = exp(-x)` the two infinite values are at most `1 / x` and `1 / x^2`: the first is
`1 / (exp x - 1)` and uses `x ≤ exp x - 1`; the second is `1 / (2 sinh (x / 2))^2` and uses
`|x / 2| ≤ |sinh (x / 2)|`. Both inequalities hold for every real `x`, with both sides zero at
`x = 0` by the convention `1 / 0 = 0`. The finite exponential sum needs `0 < x`.

The power bound `(W + y)^n ≤ W^n exp(n y / W)` for `W > 0` and `W + y ≥ 0` turns a polynomial
upper bound into an exponential one. Finally `⌈a / b⌉ ≤ a / b + 1` after casting to a linearly
ordered field, for all natural `a, b`.

## Main statements

* `sum_range_pow_succ_le_div_one_sub`
* `sum_range_natCast_succ_mul_pow_succ_mul_one_sub_sq`,
  `sum_range_natCast_succ_mul_pow_succ_le`
* `sum_range_linear_mul_pow_succ_le`
* `Real.exp_neg_div_one_sub_exp_neg_le`, `Real.exp_neg_div_one_sub_exp_neg_sq_le`,
  `Real.sum_range_linear_mul_exp_neg_pow_succ_le`
* `Real.add_pow_le_pow_mul_exp`
* `Nat.cast_ceilDiv_le_div_add_one`
-/

@[expose] public section

open Finset

section OrderedField

variable {K : Type*}

/-- The closed form of the linearly weighted geometric sum, in every commutative ring:
`(1 - q)^2 ∑_{j<m} (j+1) q^(j+1) = q - (m+1) q^(m+1) + m q^(m+2)`. -/
theorem sum_range_natCast_succ_mul_pow_succ_mul_one_sub_sq [CommRing K] (q : K) (m : ℕ) :
    (∑ j ∈ range m, ((j + 1 : ℕ) : K) * q ^ (j + 1)) * (1 - q) ^ 2 =
      q - (m + 1) * q ^ (m + 1) + m * q ^ (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, add_mul, ih]
      push_cast
      ring

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For `0 ≤ q < 1`, every finite geometric sum starting at `q` is at most `q / (1 - q)`. -/
theorem sum_range_pow_succ_le_div_one_sub (m : ℕ) {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ j ∈ range m, q ^ (j + 1) ≤ q / (1 - q) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1) hq0 hq1
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel, pow_one] at h
  simpa only [add_comm 1] using h

/-- For `0 ≤ q < 1`, `∑_{j<m} (j+1) q^(j+1) ≤ q / (1 - q)^2`. The deficit is
`q^(m+1) ((m+1) - m q) / (1 - q)^2`, which is nonnegative because `q ≥ 0` and `q ≤ 1`. -/
theorem sum_range_natCast_succ_mul_pow_succ_le (m : ℕ) {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ j ∈ range m, ((j + 1 : ℕ) : K) * q ^ (j + 1) ≤ q / (1 - q) ^ 2 := by
  have hpos : 0 < (1 - q) ^ 2 := pow_pos (sub_pos.mpr hq1) 2
  rw [le_div_iff₀ hpos, sum_range_natCast_succ_mul_pow_succ_mul_one_sub_sq]
  have hdef : 0 ≤ q ^ (m + 1) * ((m + 1) - m * q) := by
    refine mul_nonneg (pow_nonneg hq0 _) ?_
    have hm : (0 : K) ≤ m := Nat.cast_nonneg m
    nlinarith
  nlinarith [pow_succ q (m + 1)]

/-- For `0 ≤ q < 1` and `a, b ≥ 0`,
`∑_{j<m} (a (j+1) + b) q^(j+1) ≤ a q / (1 - q)^2 + b q / (1 - q)`. The signs of `a` and `b` are
needed because the two geometric bounds are only upper bounds. -/
theorem sum_range_linear_mul_pow_succ_le (m : ℕ) {a b q : K} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ j ∈ range m, (a * ((j + 1 : ℕ) : K) + b) * q ^ (j + 1) ≤
      a * (q / (1 - q) ^ 2) + b * (q / (1 - q)) := by
  simp_rw [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left (sum_range_natCast_succ_mul_pow_succ_le m hq0 hq1) ha)
    (mul_le_mul_of_nonneg_left (sum_range_pow_succ_le_div_one_sub m hq0 hq1) hb)

/-- The ceiling of `a / b`, cast to a linearly ordered field, is at most `a / b + 1`. No
hypothesis on `b` is needed: for `b = 0` both `a ⌈/⌉ 0` and `a / 0` are zero. -/
theorem Nat.cast_ceilDiv_le_div_add_one (a b : ℕ) :
    ((a ⌈/⌉ b : ℕ) : K) ≤ (a : K) / b + 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hb' : (0 : K) < b := Nat.cast_pos.mpr hb
  refine Nat.cast_div_le.trans ?_
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, div_le_iff₀ hb', add_mul,
    div_mul_cancel₀ _ hb'.ne']
  linarith

end OrderedField

namespace Real

/-- `exp (-x) / (1 - exp (-x)) ≤ 1 / x` for every real `x`. The left side is
`1 / (exp x - 1)`, and `x ≤ exp x - 1`; for `x < 0` both sides are negative and the
reciprocal reverses the order the other way. At `x = 0` both sides are zero. -/
theorem exp_neg_div_one_sub_exp_neg_le (x : ℝ) :
    exp (-x) / (1 - exp (-x)) ≤ 1 / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hne : exp x - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, exp_eq_one_iff]
    exact hx
  have heq : exp (-x) / (1 - exp (-x)) = 1 / (exp x - 1) := by
    rw [exp_neg]
    field_simp
  have hle : x ≤ exp x - 1 := by linarith [add_one_le_exp x]
  rw [heq]
  rcases hx.lt_or_gt with hneg | hpos
  · exact one_div_le_one_div_of_neg_of_le (by linarith [exp_lt_one_iff.mpr hneg]) hle
  · exact one_div_le_one_div_of_le hpos hle

/-- The positive-argument case of `exp_neg_div_one_sub_exp_neg_sq_le`, from `x / 2 ≤ sinh (x / 2)`
and `(1 - exp (-x)) = 2 sinh (x / 2) exp (-x / 2)`. -/
private theorem exp_neg_div_one_sub_exp_neg_sq_le_of_pos {x : ℝ} (hx : 0 < x) :
    exp (-x) / (1 - exp (-x)) ^ 2 ≤ 1 / x ^ 2 := by
  have hq : exp (-x) < 1 := by rw [exp_lt_one_iff]; linarith
  have hs := self_le_sinh_iff.mpr (by linarith : 0 ≤ x / 2)
  rw [sinh_eq] at hs
  have hab : exp (x / 2) * exp (-(x / 2)) = 1 := by rw [← exp_add]; simp
  have hb : exp (-(x / 2)) ^ 2 = exp (-x) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hs (exp_pos (-(x / 2))).le
  have hlinear : x * exp (-(x / 2)) ≤ 1 - exp (-x) := by nlinarith
  have hsq := pow_le_pow_left₀ (by positivity) hlinear 2
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos hx 2)]
  nlinarith

/-- `exp (-x) / (1 - exp (-x))^2 ≤ 1 / x^2` for every real `x`. The left side is
`1 / (2 sinh (x / 2))^2`, which is even in `x`, and `|x / 2| ≤ |sinh (x / 2)|`. At `x = 0` both
sides are zero. -/
theorem exp_neg_div_one_sub_exp_neg_sq_le (x : ℝ) :
    exp (-x) / (1 - exp (-x)) ^ 2 ≤ 1 / x ^ 2 := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have h := exp_neg_div_one_sub_exp_neg_sq_le_of_pos (neg_pos.mpr hneg)
    have hne : 1 - exp x ≠ 0 := by
      rw [sub_ne_zero, ne_comm, Ne, exp_eq_one_iff]
      exact hneg.ne
    have heq : exp (-x) / (1 - exp (-x)) ^ 2 = exp x / (1 - exp x) ^ 2 := by
      have hne' : exp x - 1 ≠ 0 := fun h => hne (by linarith)
      rw [exp_neg]
      field_simp
      ring
    rw [heq]
    simpa using h
  · simp
  · exact exp_neg_div_one_sub_exp_neg_sq_le_of_pos hpos

/-- For `x > 0` and `a, b ≥ 0`,
`∑_{j<m} (a (j+1) + b) exp(-x)^(j+1) ≤ a / x^2 + b / x`. The hypothesis `0 < x` is needed: at
`x = 0` every term is `a (j+1) + b` while the right side is zero. -/
theorem sum_range_linear_mul_exp_neg_pow_succ_le (m : ℕ) {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 < x) :
    ∑ j ∈ range m, (a * ((j + 1 : ℕ) : ℝ) + b) * exp (-x) ^ (j + 1) ≤ a / x ^ 2 + b / x := by
  have hq : exp (-x) < 1 := by rw [exp_lt_one_iff]; linarith
  refine (sum_range_linear_mul_pow_succ_le m ha hb (exp_pos _).le hq).trans ?_
  rw [div_eq_mul_one_div a, div_eq_mul_one_div b]
  exact add_le_add (mul_le_mul_of_nonneg_left (exp_neg_div_one_sub_exp_neg_sq_le x) ha)
    (mul_le_mul_of_nonneg_left (exp_neg_div_one_sub_exp_neg_le x) hb)

/-- For `W > 0` and `W + y ≥ 0`, `(W + y)^n ≤ W^n exp(n y / W)`, from `1 + y / W ≤ exp (y / W)`.
Both hypotheses are needed: for `W = 0`, `y = 1`, `n = 1` the left side is `1` and the right side
is `0`; for `W = 1`, `y = -3`, `n = 2` the left side is `4` and the right side is `exp (-6)`. -/
theorem add_pow_le_pow_mul_exp (n : ℕ) {W y : ℝ} (hW : 0 < W) (hWy : 0 ≤ W + y) :
    (W + y) ^ n ≤ W ^ n * exp (n * (y / W)) := by
  have hbase : W + y ≤ W * exp (y / W) := by
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp (y / W)) hW.le
    rwa [mul_add, mul_div_cancel₀ _ hW.ne', mul_one, add_comm y] at h
  calc
    (W + y) ^ n ≤ (W * exp (y / W)) ^ n := pow_le_pow_left₀ hWy hbase n
    _ = W ^ n * exp (n * (y / W)) := by rw [mul_pow, ← exp_nat_mul]

end Real
