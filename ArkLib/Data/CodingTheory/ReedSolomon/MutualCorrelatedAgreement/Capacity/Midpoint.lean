/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Order.FloorHalf
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Midpoint thresholds for correlated agreement

For a proximity parameter `δ`, block length `n` and dimension `k`, the midpoint threshold is
`k + ⌊δ * n / 2⌋₊`. When the agreement threshold `A` satisfies `k + δ * n ≤ A ≤ n`, the midpoint
lies between `k` and `A`, and both integer gaps (to `k` and to `A`, each plus one) are at least
`δ * n / 2`.

## Main statements

* `ReedSolomon.correlatedMidpoint`: the threshold `k + ⌊δ * n / 2⌋₊`.
* `ReedSolomon.correlatedMidpoint_bounds`: the five bounds.

## References

Ported from `Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/Midpoint.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `correlatedMidpoint` and
`correlatedMidpoint_bounds` keep the source statements. The proof of the gap bounds moved to
`Nat.add_floor_half_bounds` in `ArkLib/ToMathlib/Order/FloorHalf.lean`, which works over any
ordered field with a floor; the bound `correlatedMidpoint δ n k ≤ n` is the only part that uses
`A ≤ n`.
-/

@[expose] public section

namespace ReedSolomon

/-- The midpoint threshold `k + ⌊δ * n / 2⌋₊` between the dimension `k` and an agreement threshold
at least `k + δ * n`. For `δ * n < 2` it equals `k`. -/
noncomputable def correlatedMidpoint (δ : ℝ) (n k : ℕ) : ℕ :=
  k + ⌊δ * n / 2⌋₊

/-- **Midpoint bounds.** If `0 ≤ δ` and `k + δ * n ≤ A ≤ n`, then
`k ≤ correlatedMidpoint δ n k ≤ A ≤ n`, and both `A - m + 1` and `m - k + 1`, for
`m = correlatedMidpoint δ n k`, are at least `δ * n / 2`.

`0 ≤ δ` is needed for `m ≤ A` (see `Nat.add_floor_half_bounds`); `A ≤ n` is used only for
`m ≤ n`. The `+ 1` in the gaps covers `δ * n < 2`, where `m = k`. -/
theorem correlatedMidpoint_bounds (δ : ℝ) (n k A : ℕ)
    (hδ : 0 ≤ δ) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    k ≤ correlatedMidpoint δ n k ∧ correlatedMidpoint δ n k ≤ A ∧
      correlatedMidpoint δ n k ≤ n ∧
      δ * n / 2 ≤ ((A - correlatedMidpoint δ n k + 1 : ℕ) : ℝ) ∧
      δ * n / 2 ≤ ((correlatedMidpoint δ n k - k + 1 : ℕ) : ℝ) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    Nat.add_floor_half_bounds (mul_nonneg hδ (Nat.cast_nonneg n)) hgap
  exact ⟨h₁, h₂, h₂.trans hAn, h₃, h₄⟩

end ReedSolomon
