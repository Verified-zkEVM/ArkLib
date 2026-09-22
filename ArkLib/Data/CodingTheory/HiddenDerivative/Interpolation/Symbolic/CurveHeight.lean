/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The interpolation height for polynomial curves

The finite interpolation-height certificate for a received line compares, at height `h`, the
number of coefficient slots `rows * (h + 1)` with the number of available slots
`∑ i ∈ s, count i * (h + 1 - weight i)`, where column class `i` occurs `count i` times and has
challenge-degree budget `weight i`. Replacing the line by a curve of degree `ℓ` multiplies each
budget by `ℓ`. At the height `H = ℓ * (h + 1) - 1` both sides of the comparison are multiplied by
exactly `ℓ`, so a strict line certificate gives a strict curve certificate. This file proves only
this arithmetic transfer; it does not construct an interpolant.

## Main statements

* `curveInterpolationHeight ℓ h = ℓ * (h + 1) - 1`, with `curveInterpolationHeight_succ` and
  `curveInterpolationHeight_column` for `0 < ℓ`.
* `curveInterpolationHeight_preserves_certificate`: the strict comparison transfers, for every
  `ℓ`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 5.6, Proposition 5.10, (64)
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- The height `ℓ * (h + 1) - 1` for a curve of degree `ℓ`, lifted from the line height `h`. -/
def curveInterpolationHeight (ℓ h : ℕ) : ℕ := ℓ * (h + 1) - 1

/-- For `0 < ℓ` the number of coefficient slots `H + 1` at the curve height is `ℓ * (h + 1)`.
The hypothesis is needed: for `ℓ = 0` the height is `0` and the left side is `1`. -/
theorem curveInterpolationHeight_succ {ℓ : ℕ} (hℓ : 0 < ℓ) (h : ℕ) :
    curveInterpolationHeight ℓ h + 1 = ℓ * (h + 1) :=
  Nat.sub_add_cancel (Nat.mul_pos hℓ (Nat.succ_pos h))

/-- For `0 < ℓ` the available slots of a column with curve budget `ℓ * a` are `ℓ` times those of
the line column with budget `a`, including the case `h + 1 ≤ a` where both are `0` by truncated
subtraction. The hypothesis is needed, as in `curveInterpolationHeight_succ`. -/
theorem curveInterpolationHeight_column {ℓ : ℕ} (hℓ : 0 < ℓ) (h a : ℕ) :
    curveInterpolationHeight ℓ h + 1 - ℓ * a = ℓ * (h + 1 - a) := by
  rw [curveInterpolationHeight_succ hℓ, Nat.mul_sub_left_distrib]

/-- A strict line certificate `rows * (h + 1) < ∑ i ∈ s, count i * (h + 1 - weight i)` remains
strict at the curve height with budgets `ℓ * weight i`. For `0 < ℓ` both sides are multiplied by
`ℓ`. For `ℓ = 0` the curve height is `0` and the conclusion is `rows < ∑ i ∈ s, count i`, which
follows from the line certificate because `h + 1 - weight i ≤ h + 1`. -/
theorem curveInterpolationHeight_preserves_certificate {ι : Type*} (s : Finset ι)
    (count weight : ι → ℕ) (rows h ℓ : ℕ)
    (hcertificate : rows * (h + 1) < ∑ i ∈ s, count i * (h + 1 - weight i)) :
    rows * (curveInterpolationHeight ℓ h + 1) <
      ∑ i ∈ s, count i * (curveInterpolationHeight ℓ h + 1 - ℓ * weight i) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [curveInterpolationHeight, zero_mul, Nat.zero_sub, zero_add, Nat.sub_zero, mul_one]
    have hle : ∑ i ∈ s, count i * (h + 1 - weight i) ≤ (∑ i ∈ s, count i) * (h + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact Nat.lt_of_mul_lt_mul_right (hcertificate.trans_le hle)
  · simp_rw [curveInterpolationHeight_column hℓ, Nat.mul_left_comm (count _) ℓ]
    rw [← Finset.mul_sum, curveInterpolationHeight_succ hℓ, Nat.mul_left_comm rows ℓ]
    exact Nat.mul_lt_mul_of_pos_left hcertificate hℓ

end ReedSolomon.HiddenDerivative
