/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.Staircase

/-!
# Staircase count acceptance tests

Concrete counts from the theorems, the slope `D = 0` where the finite staircase and the unbounded
pair type disagree, and the source-shaped statement `card_staircasePairs`.
-/

open Finset

/-- Slope `2`, length `5`: `5 + 3 + 1 = 9` pairs, one column per `b ∈ {0, 1, 2}`. -/
example : #(staircase 2 5) = 9 := by
  rw [card_staircase]
  decide

/-- The unbounded pair type has the same count for positive slope. -/
example : Nat.card {p : ℕ × ℕ // p.1 + 2 * p.2 < 5} = 9 := by
  rw [Nat.card_staircasePairs (by decide)]
  decide

/-- Slope `1` gives the triangle `x + b < L` with `L (L + 1) / 2` pairs. -/
example : Nat.staircaseCount 1 4 = 10 := by decide

/-- A slope larger than the length leaves only the column `b = 0`. -/
example : #(staircase 7 5) = 5 := by
  rw [card_staircase]
  decide

/-- At slope `0` the cut `b < L` keeps the staircase finite, with `L * L` pairs. -/
example : #(staircase 0 3) = 9 := by
  rw [card_staircase]
  decide

/-- At slope `0` the pair `(0, 1)` satisfies `0 + 0 * 1 < 1` but is not in the staircase, so
`mem_staircase_of_pos` needs `0 < D`. -/
example : (0, 1) ∉ staircase 0 1 ∧ (0 : ℕ) + 0 * 1 < 1 := by decide

/-- At slope `0` the unbounded pair type is infinite, so its `Nat.card` is `0`, not
`staircaseCount 0 1 = 1`: `card_staircasePairs` needs `0 < D`. -/
example : Nat.card {p : ℕ × ℕ // p.1 + 0 * p.2 < 1} ≠ Nat.staircaseCount 0 1 := by
  have : Infinite {p : ℕ × ℕ // p.1 + 0 * p.2 < 1} :=
    Infinite.of_injective (fun b : ℕ => ⟨(0, b), by simp⟩) fun a b h => by
      simpa using congrArg (fun p : {p : ℕ × ℕ // p.1 + 0 * p.2 < 1} => p.1.2) h
  rw [Nat.card_eq_zero_of_infinite]
  decide
