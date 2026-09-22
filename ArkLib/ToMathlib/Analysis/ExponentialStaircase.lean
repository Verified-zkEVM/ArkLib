/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# An exponential bound for a descending staircase sum

For `m : ℕ`, `c ≥ 0` and `t > 0`,

  `∑ s < m, (m - s + c) * exp (t * s) ≤ exp (t * m) * ((c + 1) / t + 1 / t ^ 2)`.

The integral of `(m - s + c) * exp (t * s)` over `[0, m]` is at most
`exp (t * m) * (c / t + 1 / t ^ 2)`; the discrete sum costs the extra `1 / t` from `c + 1`.
The proof is discrete: with `F s = exp (t * s) * ((m - s + c + 1) / t + 1 / t ^ 2)`, each summand
is at most `F (s + 1) - F s` by `1 + t ≤ exp t`, and the sum telescopes to `F m - F 0 ≤ F m`.

## Main statements

* `Real.sum_staircase_mul_exp_le` — the displayed bound.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Analysis/ExponentialStaircase.lean`: `Real.sum_staircase_mul_exp_le`, with the
same statement. Its source consumer (`RatePartition/RankEstimate.lean`) is not yet ported.
-/

@[expose] public section

/-- For `m : ℕ`, `c ≥ 0` and `t > 0`,
`∑ s < m, (m - s + c) * exp (t * s) ≤ exp (t * m) * ((c + 1) / t + 1 / t ^ 2)`.

Both hypotheses are needed. At `t = 0`, `m = 1`, `c = 0` the left side is `1` and the right side
is `0` (division by zero). At `m = 1`, `t = 1`, `c = -10` the left side is `-9` and the right side
is `-8 * exp 1 < -9`. -/
theorem Real.sum_staircase_mul_exp_le (m : ℕ) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    (∑ s ∈ Finset.range m, ((m : ℝ) - s + c) * Real.exp (t * s)) ≤
      Real.exp (t * m) * ((c + 1) / t + 1 / t ^ 2) := by
  let F := fun s : ℕ ↦ Real.exp (t * s) * (((m : ℝ) - s + c + 1) / t + 1 / t ^ 2)
  have hstep : ∀ s ∈ Finset.range m,
      ((m : ℝ) - s + c) * Real.exp (t * s) ≤ F (s + 1) - F s := by
    intro s hs
    have hs' : (s : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hs).le
    have hB : 0 ≤ ((m : ℝ) - s + c) / t + 1 / t ^ 2 := by positivity
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) hB
    have hid : t * (((m : ℝ) - s + c) / t + 1 / t ^ 2) - 1 / t = (m : ℝ) - s + c := by
      field_simp; ring
    have hgap : (m : ℝ) - s + c ≤
        Real.exp t * (((m : ℝ) - s + c) / t + 1 / t ^ 2) -
          (((m : ℝ) - s + c + 1) / t + 1 / t ^ 2) := by
      have hsplit : ((m : ℝ) - s + c + 1) / t + 1 / t ^ 2 =
          (((m : ℝ) - s + c) / t + 1 / t ^ 2) + 1 / t := by ring
      rw [hsplit]
      nlinarith only [he, hid]
    have hscaled := mul_le_mul_of_nonneg_left hgap (Real.exp_pos (t * s)).le
    dsimp [F]
    rw [Nat.cast_add, Nat.cast_one, show t * ((s : ℝ) + 1) = t * s + t by ring, Real.exp_add]
    ring_nf at hscaled ⊢
    exact hscaled
  calc
    _ ≤ ∑ s ∈ Finset.range m, (F (s + 1) - F s) := Finset.sum_le_sum hstep
    _ = F m - F 0 := Finset.sum_range_sub F m
    _ ≤ F m := sub_le_self _ (by
      simp only [F, Nat.cast_zero, sub_zero, mul_zero, Real.exp_zero, one_mul]
      positivity)
    _ = _ := by simp [F]
