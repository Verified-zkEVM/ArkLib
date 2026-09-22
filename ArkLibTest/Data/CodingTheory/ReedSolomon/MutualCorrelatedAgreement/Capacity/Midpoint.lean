/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Midpoint

/-!
# Acceptance tests for the midpoint threshold

With `δ = 1 / 2`, `n = 10`, `k = 2` and `A = 8`, the midpoint is `2 + ⌊5 / 2⌋₊ = 4`, and the gaps
`A - 4 + 1 = 5` and `4 - 2 + 1 = 3` are at least `5 / 2`. With `δ = 0` the midpoint is `k`.
-/

namespace ReedSolomon.MidpointTest

example : correlatedMidpoint (1 / 2) 10 2 = 4 := by
  rw [correlatedMidpoint, (Nat.floor_eq_iff (by norm_num) :
    ⌊(1 / 2 : ℝ) * (10 : ℕ) / 2⌋₊ = 2 ↔ _).mpr ⟨by norm_num, by norm_num⟩]

example : correlatedMidpoint (1 / 2) 10 2 ≤ 8 ∧
    (1 / 2 : ℝ) * (10 : ℕ) / 2 ≤ ((8 - correlatedMidpoint (1 / 2) 10 2 + 1 : ℕ) : ℝ) := by
  obtain ⟨-, h, -, h', -⟩ := correlatedMidpoint_bounds (1 / 2) 10 2 8 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩

/-- With `δ = 0` the midpoint is the dimension. -/
example (n k : ℕ) : correlatedMidpoint 0 n k = k := by simp [correlatedMidpoint]

end ReedSolomon.MidpointTest
