/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Midpoint

/-! # Acceptance case for correlated-agreement capacity bounds -/

open ReedSolomon

example : correlatedMidpoint (1 / 2) 10 2 ≤ 8 ∧
    (1 / 2 : ℝ) * (10 : ℕ) / 2 ≤ ((8 - correlatedMidpoint (1 / 2) 10 2 + 1 : ℕ) : ℝ) := by
  obtain ⟨-, h, -, h', -⟩ := correlatedMidpoint_bounds (1 / 2) 10 2 8 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩
