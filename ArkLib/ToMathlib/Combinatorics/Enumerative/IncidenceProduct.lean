/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.Lemmas
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

This file defines these products and proves their elementary properties.

* `incidenceProduct n A b T d` is the product of the factors with threshold `T t` at dimension
  `t + 1`, for `t < d`.
* `dimensionSensitiveIncidenceProduct n A k b d` uses, at dimension `t + 1`, the factor
  `((n - k + t + 1) * b) / (A - k + t + 1)`. For `t < k ≤ A ≤ n` this is the factor with
  threshold `T = k - t`: a positive-dimensional component of dimension `t + 1` in the space of
  polynomials of degree less than `k` lies in at most `k - (t + 1)` evaluation equations at
  distinct points.
* `hybridDimensionSensitiveIncidenceProduct n A L k b d` uses the threshold `L` in dimension one
  and the threshold `k + 1 - t` in dimension `t + 1` for `t ≥ 1`.

Every factor is at least one when `A ≤ n` and `0 < b`, whatever the threshold, so under these
hypotheses the products are monotone in the dimension. The ratio `(n - m) / (A - m)` increases
with `m` for `m < A ≤ n`, which is how the number of identically vanishing equations is compared
with a threshold.

## Main statements

* `natCast_sub_div_natCast_sub_le`: `(n - m) / (A - m) ≤ (n - m') / (A - m')` for
  `m ≤ m' < A ≤ n`.
* `one_le_incidenceFactor`: each factor is at least one when `A ≤ n` and `0 < b`.
* `natCast_sub_mul_le_incidenceFactor_mul`: for `j < T ≤ A ≤ n`, the factor with threshold `T`
  bounds `(n - j) * b / (A - j)`, which makes it an admissible ratio in an incidence induction.
* `incidenceProduct_const`, `incidenceProduct_mono_dimension`: the product with a constant
  threshold is a power, and the product is monotone in the dimension when `A ≤ n` and `0 < b`.
* `dimensionSensitiveIncidenceProduct_eq_incidenceProduct`,
  `hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct`: the two named products as
  products with a threshold function.
* `dimensionSensitiveIncidenceProduct_eq_pow_mul`: the degree bound `b` contributes `b ^ d`.
* `dimensionSensitiveIncidenceProduct_le_one`: the products in dimension at most one are bounded
  by the first factor.
* `natCast_shiftedRatio_le_one_div` and
  `dimensionSensitiveIncidenceProduct_le_one_div_pow_of_gap`: shifted ratios and their products
  are bounded by powers of `1 / δ` under a linear gap condition.
* `dimensionSensitiveIncidenceProduct_mono_dimension` and
  `dimensionSensitiveIncidenceProduct_le_first_pow`: monotonicity and a fixed-threshold power
  bound.
* `hybridDimensionSensitiveIncidenceProduct_mono_dimension`,
  `hybridDimensionSensitiveIncidenceProduct_eq_factor_mul`,
  `hybridDimensionSensitiveIncidenceProduct_min_le`,
  `hybridDimensionSensitiveIncidenceProduct_le_two`: monotonicity, a factorization below the
  coefficient dimension, and upper bounds by initial factors.

## References

* [DKT26]
-/

@[expose] public section

/-- For `m ≤ m' < A ≤ n`, the ratio `(n - m) / (A - m)` is at most `(n - m') / (A - m')`:
removing the same number of elements from a larger and a smaller count increases their ratio. -/
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

/-- If `0 < δ ≤ 1` and `δ * x ≤ y`, then the ratio `(x + j + 1) / (y + j + 1)` is at most
`1 / δ`. -/
theorem natCast_shiftedRatio_le_one_div {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (δ : K)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (x y j : ℕ) (hxy : δ * x ≤ y) :
    ((x + j + 1 : ℕ) : K) / ((y + j + 1 : ℕ) : K) ≤ 1 / δ := by
  have hden : (0 : K) < ((y + j + 1 : ℕ) : K) := by positivity
  rw [div_le_div_iff₀ hden hδ]
  push_cast
  have hj : (0 : K) ≤ (j : K) + 1 := by positivity
  have hxy' := mul_le_mul_of_nonneg_right hxy hj
  have hδ' := mul_le_mul_of_nonneg_right hδone hj
  nlinarith

/-- The incidence factor `((n - T + 1) * b) / (A - T + 1)` is at least one when `A ≤ n` and
`0 < b`, for every threshold `T`. -/
theorem one_le_incidenceFactor {n A T b : ℕ} (hAn : A ≤ n) (hb : 0 < b) :
    (1 : ℚ) ≤ ((((n - T + 1) * b : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ)) := by
  rw [one_le_div₀ (by exact_mod_cast (show 0 < A - T + 1 by omega))]
  exact_mod_cast (show A - T + 1 ≤ (n - T + 1) * b from
    (by omega : A - T + 1 ≤ n - T + 1).trans (Nat.le_mul_of_pos_right _ hb))

/-- For `j < T ≤ A ≤ n`, `(n - j) * (A - T + 1) ≤ (n - T + 1) * (A - j)`: removing `j` of `n`
elements and `j` of `A` elements gives a ratio at most the ratio for `T - 1` removed. -/
private theorem sub_mul_sub_add_one_le {n A T j : ℕ} (hj : j < T) (hTA : T ≤ A)
    (hAn : A ≤ n) :
    (n - j) * (A - T + 1) ≤ (n - T + 1) * (A - j) := by
  obtain ⟨z, rfl⟩ : ∃ z, T = j + 1 + z := ⟨T - j - 1, by omega⟩
  rw [show n - j = (n - (j + 1 + z) + 1) + z by omega,
    show A - j = (A - (j + 1 + z) + 1) + z by omega]
  have : A - (j + 1 + z) + 1 ≤ n - (j + 1 + z) + 1 := by omega
  nlinarith

/-- For `j < T ≤ A ≤ n`, the incidence factor `((n - T + 1) * b) / (A - T + 1)` is an admissible
ratio at `j`: `(n - j) * b ≤ ((n - T + 1) * b) / (A - T + 1) * (A - j)`. -/
theorem natCast_sub_mul_le_incidenceFactor_mul {n A T b j : ℕ} (hj : j < T) (hTA : T ≤ A)
    (hAn : A ≤ n) :
    (((n - j) * b : ℕ) : ℚ) ≤
      ((((n - T + 1) * b : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ)) * ((A - j : ℕ) : ℚ) := by
  have hc : (0 : ℚ) < ((A - T + 1 : ℕ) : ℚ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc, ← Nat.cast_mul, ← Nat.cast_mul]
  have := Nat.mul_le_mul_right b (sub_mul_sub_add_one_le hj hTA hAn)
  exact_mod_cast (by nlinarith : (n - j) * b * (A - T + 1) ≤ (n - T + 1) * b * (A - j))

/-- The product over `t < d` of the incidence factors `((n - T t + 1) * b) / (A - T t + 1)` with
threshold `T t` at dimension `t + 1`. -/
def incidenceProduct (n A b : ℕ) (T : ℕ → ℕ) (d : ℕ) : ℚ :=
  ∏ t ∈ Finset.range d, ((((n - T t + 1) * b : ℕ) : ℚ) / ((A - T t + 1 : ℕ) : ℚ))

/-- The product of incidence factors is nonnegative. -/
theorem incidenceProduct_nonneg (n A b : ℕ) (T : ℕ → ℕ) (d : ℕ) :
    0 ≤ incidenceProduct n A b T d :=
  Finset.prod_nonneg fun _ _ ↦ div_nonneg (by positivity) (by positivity)

/-- With the constant threshold `L`, the product up to dimension `d` is the `d`-th power of the
factor `((n - L + 1) * b) / (A - L + 1)`. -/
theorem incidenceProduct_const (n A b L d : ℕ) :
    incidenceProduct n A b (fun _ ↦ L) d =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  rw [incidenceProduct, Finset.prod_const, Finset.card_range]

/-- If `A ≤ n` and `0 < b`, every factor is at least one, so the product is monotone in the
dimension. -/
theorem incidenceProduct_mono_dimension {n A b : ℕ} (T : ℕ → ℕ) (hAn : A ≤ n)
    (hb : 0 < b) :
    Monotone (incidenceProduct n A b T) :=
  monotone_nat_of_le_succ fun d ↦ by
    simpa only [incidenceProduct, Finset.prod_range_succ] using
      (le_mul_of_one_le_right (incidenceProduct_nonneg n A b T d)
        (one_le_incidenceFactor hAn hb))

/-- The product over `t < d` of the factors `((n - k + t + 1) * b) / (A - k + t + 1)`. -/
def dimensionSensitiveIncidenceProduct (n A k b : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 => dimensionSensitiveIncidenceProduct n A k b d *
      ((((n - k + d + 1) * b : ℕ) : ℚ) / ((A - k + d + 1 : ℕ) : ℚ))

/-- The product up to dimension `d + 1` is the product up to dimension `d` times the factor
`((n - k + d + 1) * b) / (A - k + d + 1)`. -/
theorem dimensionSensitiveIncidenceProduct_succ (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b (d + 1) =
      dimensionSensitiveIncidenceProduct n A k b d *
        ((((n - k + d + 1) * b : ℕ) : ℚ) / ((A - k + d + 1 : ℕ) : ℚ)) := rfl

/-- The product of incidence factors is nonnegative. -/
theorem dimensionSensitiveIncidenceProduct_nonneg (n A k b d : ℕ) :
    0 ≤ dimensionSensitiveIncidenceProduct n A k b d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [dimensionSensitiveIncidenceProduct_succ]
    exact mul_nonneg ih (div_nonneg (by positivity) (by positivity))

/-- The degree bound `b` contributes the factor `b ^ d` to the product up to dimension `d`. -/
theorem dimensionSensitiveIncidenceProduct_eq_pow_mul (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b d =
      (b : ℚ) ^ d * dimensionSensitiveIncidenceProduct n A k 1 d := by
  induction d with
  | zero => simp [dimensionSensitiveIncidenceProduct]
  | succ d ih =>
    rw [dimensionSensitiveIncidenceProduct_succ, dimensionSensitiveIncidenceProduct_succ, ih,
      pow_succ]
    push_cast
    ring

/-- For `d ≤ k + 1` and `k ≤ A ≤ n`, the dimension-sensitive product is the incidence product
with threshold `k - t` at dimension `t + 1`. -/
theorem dimensionSensitiveIncidenceProduct_eq_incidenceProduct {n A k b d : ℕ} (hd : d ≤ k + 1)
    (hkA : k ≤ A) (hAn : A ≤ n) :
    dimensionSensitiveIncidenceProduct n A k b d = incidenceProduct n A b (fun t ↦ k - t) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [dimensionSensitiveIncidenceProduct_succ]
    conv_rhs => rw [incidenceProduct, Finset.prod_range_succ]
    rw [ih (by omega), incidenceProduct,
      show n - (k - d) + 1 = n - k + d + 1 by omega, show A - (k - d) + 1 = A - k + d + 1 by omega]

/-- For `d ≤ 1` and `A ≤ n`, the product with `b = 1` up to dimension `d` is at most the first
factor `(n - k + 1) / (A - k + 1)`. -/
theorem dimensionSensitiveIncidenceProduct_le_one {n A k d : ℕ} (hd : d ≤ 1) (hAn : A ≤ n) :
    dimensionSensitiveIncidenceProduct n A k 1 d ≤
      ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  interval_cases d
  · simpa [dimensionSensitiveIncidenceProduct] using
      one_le_incidenceFactor (T := k) (b := 1) hAn one_pos
  · simp [dimensionSensitiveIncidenceProduct]

/-- If `A ≤ n` and `0 < b`, the dimension-sensitive product is monotone in its dimension. -/
theorem dimensionSensitiveIncidenceProduct_mono_dimension {n A k b : ℕ} (hAn : A ≤ n)
    (hb : 0 < b) : Monotone (dimensionSensitiveIncidenceProduct n A k b) := by
  apply monotone_nat_of_le_succ
  intro d
  rw [dimensionSensitiveIncidenceProduct_succ]
  apply le_mul_of_one_le_right (dimensionSensitiveIncidenceProduct_nonneg n A k b d)
  rw [one_le_div₀ (by positivity)]
  exact_mod_cast (show A - k + d + 1 ≤ (n - k + d + 1) * b from
    (by omega : A - k + d + 1 ≤ n - k + d + 1).trans (Nat.le_mul_of_pos_right _ hb))

/-- The dimension-sensitive product with degree bound one is at most its first factor to the
requested power. -/
theorem dimensionSensitiveIncidenceProduct_le_first_pow
    (n A k r : ℕ) (hkA : k ≤ A) (hAn : A ≤ n) :
    dimensionSensitiveIncidenceProduct n A k 1 r ≤
      (((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ)) ^ r := by
  induction r with
  | zero => simp [dimensionSensitiveIncidenceProduct]
  | succ r ih =>
    rw [dimensionSensitiveIncidenceProduct_succ, pow_succ]
    apply mul_le_mul ih _ (by positivity) (by positivity)
    simp only [Nat.mul_one]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast [Nat.cast_sub hkA, Nat.cast_sub (hkA.trans hAn)]
    have hdiff : (0 : ℚ) ≤ n - A := sub_nonneg.mpr (by exact_mod_cast hAn)
    have hh := mul_nonneg hdiff (show (0 : ℚ) ≤ r by positivity)
    nlinarith

/-- If `0 < δ ≤ 1` and `k + δ * n ≤ A`, the dimension-sensitive product with degree bound one
is at most `(1 / δ) ^ r`. -/
theorem dimensionSensitiveIncidenceProduct_le_one_div_pow_of_gap {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (δ : K) (n k A r : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : K) + δ * n ≤ A) :
    ((dimensionSensitiveIncidenceProduct n A k 1 r : ℚ) : K) ≤ (1 / δ) ^ r := by
  have hkn : k ≤ n := hkA.trans hAn
  have hgap' : δ * ((n - k : ℕ) : K) ≤ ((A - k : ℕ) : K) := by
    rw [Nat.cast_sub hkn, Nat.cast_sub hkA]
    nlinarith [mul_nonneg hδ.le (show (0 : K) ≤ (k : K) by positivity)]
  let first : ℚ := (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))
  have hfirst : (first : K) ≤ 1 / δ := by
    dsimp [first]
    simpa only [Nat.add_zero, Nat.mul_one, Rat.cast_div, Rat.cast_natCast] using
      natCast_shiftedRatio_le_one_div δ hδ hδone (n - k) (A - k) 0 hgap'
  have hprod := dimensionSensitiveIncidenceProduct_le_first_pow n A k r hkA hAn
  have hprod' : ((dimensionSensitiveIncidenceProduct n A k 1 r : ℚ) : K) ≤ (first : K) ^ r := by
    have hcast :
        ((dimensionSensitiveIncidenceProduct n A k 1 r : ℚ) : K) ≤ ((first ^ r : ℚ) : K) := by
      exact_mod_cast hprod
    simpa only [Rat.cast_pow] using hcast
  exact hprod'.trans (pow_le_pow_left₀ (by positivity) hfirst r)

/-- The product over `t < d` of the factors `((n - T t + 1) * b) / (A - T t + 1)` with threshold
`T 0 = L` and `T t = k + 1 - t` for `t ≥ 1`. -/
def hybridDimensionSensitiveIncidenceProduct (n A L k b : ℕ) : ℕ → ℚ :=
  incidenceProduct n A b (fun t ↦ if t = 0 then L else k + 1 - t)

/-- The hybrid product is the incidence product with threshold `L` at dimension one and
`k + 1 - t` at dimension `t + 1` for `t ≥ 1`. -/
theorem hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct (n A L k b d : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b d =
      incidenceProduct n A b (fun t ↦ if t = 0 then L else k + 1 - t) d := rfl

/-- If `A ≤ n` and `0 < b`, every factor is at least one, so the product is monotone in the
dimension. -/
theorem hybridDimensionSensitiveIncidenceProduct_mono_dimension {n A L k b : ℕ} (hAn : A ≤ n)
    (hb : 0 < b) : Monotone (hybridDimensionSensitiveIncidenceProduct n A L k b) := by
  intro d d' hdd'
  simpa only [hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct] using
    incidenceProduct_mono_dimension (fun t ↦ if t = 0 then L else k + 1 - t) hAn hb hdd'

/-- For `s ≤ k + 1`, factor the hybrid product into its first factor and the dimension-sensitive
product. -/
theorem hybridDimensionSensitiveIncidenceProduct_eq_factor_mul
    (n A L k b s : ℕ) (hkA : k ≤ A) (hAn : A ≤ n) (hsk : s ≤ k + 1) :
    hybridDimensionSensitiveIncidenceProduct n A L k b (s + 1) =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k b s := by
  change incidenceProduct n A b (fun t ↦ if t = 0 then L else k + 1 - t) (s + 1) = _
  induction s with
  | zero => simp [incidenceProduct, dimensionSensitiveIncidenceProduct]
  | succ s ih =>
    rw [incidenceProduct, Finset.prod_range_succ]
    have ih' := ih (by omega)
    rw [incidenceProduct] at ih'
    rw [ih', dimensionSensitiveIncidenceProduct_succ]
    have hnEq : n - (if s + 1 = 0 then L else k + 1 - (s + 1)) + 1 = n - k + s + 1 := by
      simp only [show s + 1 ≠ 0 by omega, ite_false]
      omega
    have hAEq : A - (if s + 1 = 0 then L else k + 1 - (s + 1)) + 1 = A - k + s + 1 := by
      simp only [show s + 1 ≠ 0 by omega, ite_false]
      omega
    rw [hnEq, hAEq, mul_assoc]

/-- Cap the actual dimension at `k` before extending the dimension-sensitive product. -/
theorem hybridDimensionSensitiveIncidenceProduct_min_le
    (n A L k b r : ℕ) (hkA : k ≤ A) (hAn : A ≤ n) (hb : 0 < b) :
    hybridDimensionSensitiveIncidenceProduct n A L k b (min r k + 1) ≤
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k b r := by
  rw [hybridDimensionSensitiveIncidenceProduct_eq_factor_mul n A L k b (min r k) hkA hAn
    (by omega)]
  exact mul_le_mul_of_nonneg_left
    (dimensionSensitiveIncidenceProduct_mono_dimension hAn hb (Nat.min_le_left _ _))
    (by positivity)

/-- If `d ≤ 2`, `A ≤ n` and `0 < b`, the product up to dimension `d` is at most the product of
the first two factors. -/
theorem hybridDimensionSensitiveIncidenceProduct_le_two {n A L k b d : ℕ} (hd : d ≤ 2)
    (hAn : A ≤ n) (hb : 0 < b) :
    hybridDimensionSensitiveIncidenceProduct n A L k b d ≤
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  calc
    hybridDimensionSensitiveIncidenceProduct n A L k b d ≤
        hybridDimensionSensitiveIncidenceProduct n A L k b 2 :=
      hybridDimensionSensitiveIncidenceProduct_mono_dimension
        (n := n) (A := A) (L := L) (k := k) (b := b) hAn hb hd
    _ = _ := by
      simp only [hybridDimensionSensitiveIncidenceProduct, incidenceProduct]
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      simp
