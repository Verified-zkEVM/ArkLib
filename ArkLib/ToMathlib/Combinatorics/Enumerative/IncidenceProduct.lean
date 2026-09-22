/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Products of incidence ratios

Agreement incidence bounds count the points of a variety that agree with received data in at
least `A` of `n` positions. Each cut of a component of dimension `d` by one of the `n` position
equations costs a factor `((n - T + 1) * b) / (A - T + 1)`, where `b` bounds the degree of the
equations and a component of that dimension lies in fewer than `T` of the equations.
The bound for a component of dimension `d` is the product of these factors over the dimensions
`1, ..., d`.

This file defines the two products used by the incidence inductions and proves their elementary
properties.

* `dimensionSensitiveIncidenceProduct n A k b d` uses, at dimension `t + 1`, the factor
  `((n - k + t + 1) * b) / (A - k + t + 1)`. For `t < k ≤ A ≤ n` this is the factor with
  threshold `T = k - t`: a positive-dimensional component of dimension `t + 1` in the space of
  polynomials of degree less than `k` lies in at most `k - (t + 1)` evaluation equations at
  distinct points.
* `hybridDimensionSensitiveIncidenceProduct n A L k b d` uses the threshold `L` in dimension one
  and the threshold `k + 1 - t` in dimension `t + 1` for `t ≥ 1`.

Every factor is at least one when its threshold is at most `A` and `A ≤ n`, so under these
hypotheses the products are monotone in the dimension. The ratio `(n - m) / (A - m)` increases
with `m` for `m < A ≤ n`, which is how the number of identically vanishing equations is compared
with a threshold.

## Main statements

* `natCast_sub_div_natCast_sub_le`: `(n - m) / (A - m) ≤ (n - m') / (A - m')` for
  `m ≤ m' < A ≤ n`.
* `one_le_incidenceFactor`: each factor with threshold at most `A ≤ n` is at least one.
* `dimensionSensitiveIncidenceProduct_eq_pow_mul`: the degree bound `b` contributes `b ^ d`.
* `dimensionSensitiveIncidenceProduct_le_one`: the products in dimension at most one are bounded
  by the first factor.
* `hybridDimensionSensitiveIncidenceProduct_mono_dimension`,
  `hybridDimensionSensitiveIncidenceProduct_le_two`: monotonicity in the dimension, and the
  bound of the products in dimension at most two by the first two factors.
-/

@[expose] public section

/-- For `m ≤ m' < A ≤ n`, the ratio `(n - m) / (A - m)` is at most `(n - m') / (A - m')`: removing
the same number of elements from a larger and a smaller count increases their ratio. -/
theorem natCast_sub_div_natCast_sub_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n A m m' : ℕ} (hm : m ≤ m') (hm'A : m' < A) (hAn : A ≤ n) :
    ((n - m : ℕ) : K) / ((A - m : ℕ) : K) ≤ ((n - m' : ℕ) : K) / ((A - m' : ℕ) : K) := by
  rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < A - m))
    (by exact_mod_cast (by omega : 0 < A - m')), Nat.cast_sub (by omega : m ≤ n),
    Nat.cast_sub (by omega : m ≤ A), Nat.cast_sub (by omega : m' ≤ n),
    Nat.cast_sub (by omega : m' ≤ A)]
  have hnA : (A : K) ≤ n := by exact_mod_cast hAn
  have hmm : (m : K) ≤ m' := by exact_mod_cast hm
  nlinarith [mul_nonneg (sub_nonneg.mpr hnA) (sub_nonneg.mpr hmm)]

/-- The incidence factor `((n - T + 1) * b) / (A - T + 1)` is at least one when `T ≤ A ≤ n` and
`0 < b`. -/
theorem one_le_incidenceFactor {n A T b : ℕ} (hTA : T ≤ A) (hAn : A ≤ n) (hb : 0 < b) :
    (1 : ℚ) ≤ ((((n - T + 1) * b : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ)) := by
  rw [one_le_div₀ (by exact_mod_cast (show 0 < A - T + 1 by omega))]
  exact_mod_cast (show A - T + 1 ≤ (n - T + 1) * b from
    (by omega : A - T + 1 ≤ n - T + 1).trans (Nat.le_mul_of_pos_right _ hb))

/-- The product over `t < d` of the factors `((n - k + t + 1) * b) / (A - k + t + 1)`. -/
def dimensionSensitiveIncidenceProduct (n A k b : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 => dimensionSensitiveIncidenceProduct n A k b d *
      ((((n - k + d + 1) * b : ℕ) : ℚ) / ((A - k + d + 1 : ℕ) : ℚ))

/-- The empty product of incidence factors is one. -/
@[simp]
theorem dimensionSensitiveIncidenceProduct_zero (n A k b : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b 0 = 1 := rfl

/-- The product up to dimension `d + 1` is the product up to dimension `d` times the factor
`((n - k + d + 1) * b) / (A - k + d + 1)`. -/
theorem dimensionSensitiveIncidenceProduct_succ (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b (d + 1) =
      dimensionSensitiveIncidenceProduct n A k b d *
        ((((n - k + d + 1) * b : ℕ) : ℚ) / ((A - k + d + 1 : ℕ) : ℚ)) := rfl

/-- The product in dimension one is the factor `((n - k + 1) * b) / (A - k + 1)`. -/
@[simp]
theorem dimensionSensitiveIncidenceProduct_one (n A k b : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b 1 =
      ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  simp [dimensionSensitiveIncidenceProduct]

/-- The product of incidence factors is nonnegative. -/
theorem dimensionSensitiveIncidenceProduct_nonneg (n A k b d : ℕ) :
    0 ≤ dimensionSensitiveIncidenceProduct n A k b d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [dimensionSensitiveIncidenceProduct_succ]
    exact mul_nonneg ih (div_nonneg (by positivity) (by positivity))

/-- The degree bound `b` contributes the factor `b ^ d` to the product up to dimension `d`. -/
theorem dimensionSensitiveIncidenceProduct_eq_pow_mul (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b d =
      (b : ℚ) ^ d * dimensionSensitiveIncidenceProduct n A k 1 d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [dimensionSensitiveIncidenceProduct_succ, dimensionSensitiveIncidenceProduct_succ, ih,
      pow_succ]
    push_cast
    ring

/-- For `d ≤ 1` and `k ≤ A ≤ n`, the product with `b = 1` up to dimension `d` is at most the
first factor `(n - k + 1) / (A - k + 1)`. -/
theorem dimensionSensitiveIncidenceProduct_le_one {n A k d : ℕ} (hd : d ≤ 1) (hkA : k ≤ A)
    (hAn : A ≤ n) :
    dimensionSensitiveIncidenceProduct n A k 1 d ≤
      ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  interval_cases d
  · simpa using one_le_incidenceFactor (T := k) (b := 1) hkA hAn one_pos
  · simp

/-- The product over `t < d` of the factors `((n - T t + 1) * b) / (A - T t + 1)` with threshold
`T 0 = L` and `T t = k + 1 - t` for `t ≥ 1`. -/
def hybridDimensionSensitiveIncidenceProduct (n A L k b : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 => hybridDimensionSensitiveIncidenceProduct n A L k b d *
      (((((n - (if d = 0 then L else k + 1 - d) + 1) * b : ℕ) : ℚ) /
        ((A - (if d = 0 then L else k + 1 - d) + 1 : ℕ) : ℚ)))

/-- The empty product of incidence factors is one. -/
@[simp]
theorem hybridDimensionSensitiveIncidenceProduct_zero (n A L k b : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b 0 = 1 := rfl

/-- The product up to dimension `d + 1` is the product up to dimension `d` times the factor with
threshold `L` if `d = 0` and `k + 1 - d` otherwise. -/
theorem hybridDimensionSensitiveIncidenceProduct_succ (n A L k b d : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b (d + 1) =
      hybridDimensionSensitiveIncidenceProduct n A L k b d *
        (((((n - (if d = 0 then L else k + 1 - d) + 1) * b : ℕ) : ℚ) /
          ((A - (if d = 0 then L else k + 1 - d) + 1 : ℕ) : ℚ))) := rfl

/-- The product in dimension one is the factor `((n - L + 1) * b) / (A - L + 1)`. -/
@[simp]
theorem hybridDimensionSensitiveIncidenceProduct_one (n A L k b : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b 1 =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  simp [hybridDimensionSensitiveIncidenceProduct]

/-- The product in dimension two is `((n - L + 1) * b) / (A - L + 1)` times
`((n - k + 1) * b) / (A - k + 1)`. -/
@[simp]
theorem hybridDimensionSensitiveIncidenceProduct_two (n A L k b : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b 2 =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  simp [hybridDimensionSensitiveIncidenceProduct]

/-- The product of incidence factors is nonnegative. -/
theorem hybridDimensionSensitiveIncidenceProduct_nonneg (n A L k b d : ℕ) :
    0 ≤ hybridDimensionSensitiveIncidenceProduct n A L k b d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [hybridDimensionSensitiveIncidenceProduct_succ]
    exact mul_nonneg ih (div_nonneg (by positivity) (by positivity))

/-- If `L ≤ A`, `k ≤ A ≤ n` and `0 < b`, every factor is at least one, so the product is monotone
in the dimension. -/
theorem hybridDimensionSensitiveIncidenceProduct_mono_dimension {n A L k b : ℕ} (hLA : L ≤ A)
    (hkA : k ≤ A) (hAn : A ≤ n) (hb : 0 < b) :
    Monotone (hybridDimensionSensitiveIncidenceProduct n A L k b) := by
  refine monotone_nat_of_le_succ fun d ↦ ?_
  rw [hybridDimensionSensitiveIncidenceProduct_succ]
  refine le_mul_of_one_le_right (hybridDimensionSensitiveIncidenceProduct_nonneg n A L k b d) ?_
  by_cases hd : d = 0
  · subst hd
    simpa using one_le_incidenceFactor hLA hAn hb
  · simpa [hd] using one_le_incidenceFactor (T := k + 1 - d) (by omega) hAn hb

/-- If `d ≤ 2`, `L ≤ A`, `k ≤ A ≤ n` and `0 < b`, the product up to dimension `d` is at most the
product of the first two factors. -/
theorem hybridDimensionSensitiveIncidenceProduct_le_two {n A L k b d : ℕ} (hd : d ≤ 2)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n) (hb : 0 < b) :
    hybridDimensionSensitiveIncidenceProduct n A L k b d ≤
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  simpa only [hybridDimensionSensitiveIncidenceProduct_two] using
    hybridDimensionSensitiveIncidenceProduct_mono_dimension hLA hkA hAn hb hd
