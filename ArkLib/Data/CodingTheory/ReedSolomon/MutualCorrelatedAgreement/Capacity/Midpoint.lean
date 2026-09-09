/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # Midpoint thresholds for correlated agreement

The midpoint threshold supplies two positive agreement gaps, retaining half the capacity
margin on each side despite integer rounding.
-/

namespace ReedSolomon

open scoped BigOperators

/-- Midpoint between the message dimension and the guaranteed agreement threshold. -/
noncomputable def correlatedMidpoint (δ : ℝ) (n k : ℕ) : ℕ :=
  k + ⌊δ * n / 2⌋₊

/-- Both integer agreement gaps retain half the real margin, including subunit margins. -/
theorem correlatedMidpoint_bounds (δ : ℝ) (n k A : ℕ)
    (hδ : 0 ≤ δ) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    k ≤ correlatedMidpoint δ n k ∧ correlatedMidpoint δ n k ≤ A ∧
      correlatedMidpoint δ n k ≤ n ∧
      δ * n / 2 ≤ ((A - correlatedMidpoint δ n k + 1 : ℕ) : ℝ) ∧
      δ * n / 2 ≤ ((correlatedMidpoint δ n k - k + 1 : ℕ) : ℝ) := by
  have hx : 0 ≤ δ * n / 2 := by positivity
  have hf := Nat.floor_le hx
  have hf' := Nat.lt_floor_add_one (δ * n / 2)
  have hkL : k ≤ correlatedMidpoint δ n k := Nat.le_add_right _ _
  have hLA : correlatedMidpoint δ n k ≤ A := by
    unfold correlatedMidpoint
    exact_mod_cast (show (k : ℝ) + ⌊δ * n / 2⌋₊ ≤ A by linarith)
  refine ⟨hkL, hLA, hLA.trans hAn, ?_, ?_⟩
  · rw [Nat.cast_add, Nat.cast_sub hLA, Nat.cast_one]
    unfold correlatedMidpoint
    push_cast
    linarith
  · rw [Nat.cast_add, Nat.cast_sub hkL, Nat.cast_one]
    unfold correlatedMidpoint
    push_cast
    linarith


end ReedSolomon
