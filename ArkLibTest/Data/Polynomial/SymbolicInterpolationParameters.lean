/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationParameters

/-! Boundary checks for the real interpolation budgets. -/

open Polynomial.SymbolicInterpolation

-- The surplus criterion also applies at the smaller multiplicity endpoint `m = 1`.
example (z : ℝ) (hz : 3 ≤ z) : z > 2 := by
  have h := strict_surplus_of_coefficient_budget 1 (1 / 2) z (by norm_num)
    (by norm_num) (by norm_num at hz ⊢; exact hz)
  norm_num at h
  linarith

-- At full rate and the paper's smallest multiplicity, the Z budget still dominates Y.
example : (7 / 2 : ℝ) ≤ 49 / 12 := by
  have h := y_budget_le_coefficient_budget 3 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢

-- Equality in the multiplicity threshold is allowed.
example : (3 + 1 / 2 : ℝ) * (1 / 2) ≤ (1 / 2 + 1 / 12) * 3 := by
  apply x_budget_le_multiplicity_budget
  · norm_num
  · norm_num
