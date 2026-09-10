/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Scaling the finite interpolation-height certificate for polynomial curves

Replacing a received line by a degree-`ℓ` curve multiplies each column's challenge-degree
budget by `ℓ`. The height `H = ℓ(h+1)-1` preserves the strict finite dimension comparison:
every column contribution and the row budget scale by exactly `ℓ`.
This is the arithmetic height transfer, not construction of a symbolic interpolant.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), the finite-height comparison for
  polynomial curves.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- A line-height budget lifted to batching degree `ℓ`. -/
def curveInterpolationHeight (ℓ h : ℕ) : ℕ := ℓ * (h + 1) - 1

/-- Including the constant coefficient makes the lifted height exactly multiplicative. -/
theorem curveInterpolationHeight_succ {ℓ : ℕ} (hℓ : 0 < ℓ) (h : ℕ) :
    curveInterpolationHeight ℓ h + 1 = ℓ * (h + 1) := by
  unfold curveInterpolationHeight
  exact Nat.sub_add_cancel (Nat.mul_pos hℓ (Nat.succ_pos h))

/-- The available coefficient slots in each column scale even when the column is inactive.
Truncated subtraction represents the positive part in the manuscript's height test. -/
theorem curveInterpolationHeight_column {ℓ : ℕ} (hℓ : 0 < ℓ) (h a : ℕ) :
    curveInterpolationHeight ℓ h + 1 - ℓ * a = ℓ * (h + 1 - a) := by
  rw [curveInterpolationHeight_succ hℓ, Nat.mul_sub_left_distrib]

/-- A strict finite line-height certificate remains strict at the lifted curve height.
The index set describes columns or column classes; `count` records their multiplicities
and `weight` their individual challenge-degree budgets. -/
theorem curveInterpolationHeight_preserves_certificate
    {ι : Type*} (s : Finset ι) (count weight : ι → ℕ) (rows h ℓ : ℕ)
    (hℓ : 0 < ℓ)
    (hcertificate : rows * (h + 1) < ∑ i ∈ s, count i * (h + 1 - weight i)) :
    rows * (curveInterpolationHeight ℓ h + 1) <
      ∑ i ∈ s, count i * (curveInterpolationHeight ℓ h + 1 - ℓ * weight i) := by
  have hslots : ∀ i, count i * (curveInterpolationHeight ℓ h + 1 - ℓ * weight i) =
      ℓ * (count i * (h + 1 - weight i)) := by
    intro i
    rw [curveInterpolationHeight_column hℓ]
    ac_rfl
  simp_rw [hslots]
  rw [← Finset.mul_sum]
  rw [curveInterpolationHeight_succ hℓ, Nat.mul_left_comm rows ℓ]
  exact Nat.mul_lt_mul_of_pos_left hcertificate hℓ

end ReedSolomon.HiddenDerivative
