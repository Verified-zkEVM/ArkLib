/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Finset.SumRangeFrom
import Mathlib.Tactic.NormNum

/-!
# Acceptance examples for shifted finite sums

The examples compute shifted sums, split them into checked chunks, and include zero-length
chunks to check the boundary cases without positivity assumptions.
-/

namespace SumRangeFromTest

/-- The interval starting at three with length four sums to twenty-two. -/
example : Finset.sumRangeFrom (fun i : ℕ => i + 1) 3 4 = 22 := by
  norm_num [Finset.sumRangeFrom, Finset.sum_range_succ]

/-- Splitting after two terms preserves the value of the sum. -/
example : Finset.sumRangeFrom (fun i : ℕ => i + 1) 2 3 = 12 := by
  rw [Finset.sumRangeFrom_add (f := fun i : ℕ => i + 1) (start := 2) (a := 2) (b := 1)]
  norm_num [Finset.sumRangeFrom, Finset.sum_range_succ]

/-- A zero-length shifted sum is zero for any starting point. -/
example (f : ℕ → ℤ) (start : ℕ) : Finset.sumRangeFrom f start 0 = 0 := by
  simp [Finset.sumRangeFrom]

/-- Four adjacent chunks may include empty second and fourth chunks. -/
example :
    Finset.sumRangeFrom (fun i : ℕ => i + 1) 2 (1 + 0 + 2 + 0) = 12 := by
  rw [Finset.sumRangeFrom_four]
  norm_num [Finset.sumRangeFrom, Finset.sum_range_succ]

/-- The four-chunk substitution theorem combines values of adjacent sums. -/
example :
    Finset.sumRangeFrom (fun i : ℕ => i + 1) 0 (1 + 1 + 1 + 1) = 10 := by
  exact Finset.sumRangeFrom_four_eq (fun i : ℕ => i + 1) 0 1 1 1 1 1 2 3 4
    (by norm_num [Finset.sumRangeFrom, Finset.sum_range_succ])
    (by norm_num [Finset.sumRangeFrom, Finset.sum_range_succ])
    (by norm_num [Finset.sumRangeFrom, Finset.sum_range_succ])
    (by norm_num [Finset.sumRangeFrom, Finset.sum_range_succ])

/-- The two-chunk substitution theorem combines values of adjacent sums. -/
example : Finset.sumRangeFrom (fun i : ℕ => i + 1) 1 (2 + 1) = 9 := by
  exact Finset.sumRangeFrom_two_eq (fun i : ℕ => i + 1) 1 2 1 5 4
    (by norm_num [Finset.sumRangeFrom, Finset.sum_range_succ])
    (by norm_num [Finset.sumRangeFrom, Finset.sum_range_succ])

end SumRangeFromTest
