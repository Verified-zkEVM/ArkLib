/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.Staircase

/-!
# Acceptance tests for finite staircases
-/

open Finset

example : (1, 1) ∈ staircase 2 5 := by
  rw [mem_staircase_of_pos (by decide)]
  decide

example : #(staircase 2 5) = 9 := by
  rw [card_staircase]
  decide

example : Nat.card {p : ℕ × ℕ // p.1 + 2 * p.2 < 5} = 9 := by
  rw [Nat.card_staircasePairs (by decide)]
  decide
