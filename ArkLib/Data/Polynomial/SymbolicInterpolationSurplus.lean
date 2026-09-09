/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationParameters
import ArkLib.Data.Polynomial.SymbolicInterpolationSupport
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Rounded support counts for symbolic interpolation

The exact support cardinality is a polynomial when all rows have nonnegative budgets.
Its lower bound below isolates the rounding step in [BCHKS25, Lemma 3.1].

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
    *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.1.
-/

namespace Polynomial.SymbolicInterpolation

open Finset

/-- Polynomial expression for the number of monomials in untruncated rows. -/
noncomputable def variableCountPolynomial (k x y z : ℝ) : ℝ :=
  x * y * z - (x + k * z) * y * (y - 1) / 2 +
    k * y * (y - 1) * (2 * y - 1) / 6

/-- Summing real row budgets gives the variable-count polynomial, independently of rounding. -/
theorem sum_untruncated_monomial_rows (k x z : ℝ) (d : ℕ) :
    (∑ j ∈ range d, (x - k * j) * (z - j)) = variableCountPolynomial k x d z := by
  induction d with
  | zero => simp [variableCountPolynomial]
  | succ d ih =>
    rw [sum_range_succ, ih]
    simp only [variableCountPolynomial, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact cardinality as a real polynomial, under explicit nontruncation assumptions. -/
theorem card_monomialSupport_eq_polynomial (k dx d dz : ℕ)
    (hx : ∀ j < d, k * j ≤ dx) (hz : d ≤ dz) :
    ((monomialSupport k dx d dz).card : ℝ) = variableCountPolynomial k dx d dz := by
  rw [card_monomialSupport, Nat.cast_sum]
  calc
    (∑ j ∈ range d, (((dx - k * j) * (dz - j) : ℕ) : ℝ)) =
        ∑ j ∈ range d, ((dx : ℝ) - k * j) * ((dz : ℝ) - j) := by
      apply sum_congr rfl
      intro j hj
      rw [Nat.cast_mul, Nat.cast_sub (hx j (mem_range.mp hj)),
        Nat.cast_sub ((Nat.le_of_lt (mem_range.mp hj)).trans hz), Nat.cast_mul]
    _ = _ := sum_untruncated_monomial_rows k dx dz d

/-- Rounding X upward and Y upward by at most one does not decrease the paper's lower bound.
The Z budget covers the rounded Y budget, so every added row remains nonnegative. -/
theorem variableCountPolynomial_lower_bound (k x y d z : ℝ)
    (hk : 0 ≤ k) (hy : 0 ≤ y) (hyd : y ≤ d) (hdy : d ≤ y + 1)
    (hdz : d ≤ z) (hx : k * y ≤ x) :
    k * (y * (y + 1) * z / 2 - (y ^ 3 - y) / 6) ≤
      variableCountPolynomial k x d z := by
  have hd : 0 ≤ d := hy.trans hyd
  have hz : 0 ≤ z := hd.trans hdz
  have hxpart : 0 ≤ (x - k * y) * d * (2 * z - d + 1) := by
    apply mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) hd)
    linarith
  have ht : 0 ≤ d - y := sub_nonneg.mpr hyd
  have ht1 : 0 ≤ 1 - (d - y) := by linarith
  have hround : 0 ≤ k * (d - y) * (1 - (d - y)) *
      (3 * (z - y) + 1 - 2 * (d - y)) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg hk ht) ht1)
    linarith
  have hid : 6 * (variableCountPolynomial k x d z -
      k * (y * (y + 1) * z / 2 - (y ^ 3 - y) / 6)) =
      3 * ((x - k * y) * d * (2 * z - d + 1)) +
        k * (d - y) * (1 - (d - y)) * (3 * (z - y) + 1 - 2 * (d - y)) := by
    unfold variableCountPolynomial
    ring
  linarith

/-- The actual rounded monomial support dominates the real count used in the surplus criterion. -/
theorem card_monomialSupport_ceil_lower_bound (k : ℕ) (y z : ℝ)
    (hy : 0 ≤ y) (hyz : y ≤ z) :
    k * (y * (y + 1) * (⌈z⌉₊ : ℝ) / 2 - (y ^ 3 - y) / 6) ≤
      ((monomialSupport k ⌈(k : ℝ) * y⌉₊ ⌈y⌉₊ ⌈z⌉₊).card : ℝ) := by
  have hx : ∀ j < ⌈y⌉₊, k * j ≤ ⌈(k : ℝ) * y⌉₊ := by
    intro j hj
    have hjy : (j : ℝ) < y := Nat.lt_ceil.mp hj
    have h := (mul_le_mul_of_nonneg_left hjy.le (Nat.cast_nonneg k)).trans
      (Nat.le_ceil ((k : ℝ) * y))
    exact_mod_cast h
  rw [card_monomialSupport_eq_polynomial k _ _ _ hx (Nat.ceil_mono hyz)]
  exact variableCountPolynomial_lower_bound k _ y _ _ (Nat.cast_nonneg k) hy
    (Nat.le_ceil y) (Nat.ceil_lt_add_one hy).le
    (by exact_mod_cast Nat.ceil_mono hyz) (Nat.le_ceil _)

/-- The rounded supports have strictly more unknowns than point constraints at the prescribed
budgets. The identity `k = n*r²` exposes the rate without choosing a square-root representation. -/
theorem card_constraints_lt_monomials (n k m : ℕ) (r : ℝ)
    (hn : 0 < n) (hm : 3 ≤ m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hkr : (k : ℝ) = n * r ^ 2) :
    n * (constraintSupport m ⌈((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)⌉₊).card <
      (monomialSupport k ⌈(k : ℝ) * (((m : ℝ) + 1 / 2) / r)⌉₊
        ⌈((m : ℝ) + 1 / 2) / r⌉₊
        ⌈((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)⌉₊).card := by
  let y : ℝ := ((m : ℝ) + 1 / 2) / r
  let z : ℝ := ((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyz : y ≤ z := y_budget_le_coefficient_budget m r hmR hr hr1
  have hmy : (m : ℝ) ≤ y := by
    apply (le_div_iff₀ hr).mpr
    have := mul_le_mul_of_nonneg_left hr1 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hmz : m ≤ ⌈z⌉₊ := by
    exact_mod_cast hmy.trans (hyz.trans (Nat.le_ceil z))
  have heq := six_mul_card_constraintSupport m ⌈z⌉₊ hmz
  have heqR : (6 : ℝ) * (constraintSupport m ⌈z⌉₊).card + (m : ℝ) ^ 3 =
      3 * (⌈z⌉₊ : ℝ) * m * (m + 1) + m := by exact_mod_cast heq
  have hlow := card_monomialSupport_ceil_lower_bound k y z hy hyz
  have hstrict := strict_surplus_of_coefficient_budget m r (⌈z⌉₊ : ℝ)
    (by linarith) hr (Nat.le_ceil z)
  change (r ^ 2 * y * (y + 1) - (m : ℝ) * (m + 1)) * (⌈z⌉₊ : ℝ) >
    (r ^ 2 * (y ^ 3 - y) - ((m : ℝ) ^ 3 - m)) / 3 at hstrict
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled := mul_lt_mul_of_pos_left hstrict hnR
  have heqscaled := congrArg (fun a : ℝ => (n : ℝ) * a) heqR
  have hlow' : (n : ℝ) * r ^ 2 * (y * (y + 1) * (⌈z⌉₊ : ℝ) / 2 -
      (y ^ 3 - y) / 6) ≤ (monomialSupport k ⌈(k : ℝ) * y⌉₊ ⌈y⌉₊ ⌈z⌉₊).card := by
    rw [← hkr]
    exact hlow
  have hout : (n : ℝ) * (constraintSupport m ⌈z⌉₊).card <
      (monomialSupport k ⌈(k : ℝ) * y⌉₊ ⌈y⌉₊ ⌈z⌉₊).card := by
    nlinarith [hlow', hscaled, heqscaled]
  exact_mod_cast hout

end Polynomial.SymbolicInterpolation
