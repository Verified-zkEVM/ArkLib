/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationSurplus

/-! Rounded support clients, with nonintegral budgets and unequal axes. -/

open Polynomial.SymbolicInterpolation

-- The Y budget is 7/2 and the Z budget 49/12: both require upward rounding.
example : (constraintSupport 3 5).card < (monomialSupport 1 4 4 5).card := by
  have h := card_constraints_lt_monomials 1 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hy : ⌈(7 / 2 : ℝ)⌉₊ = 4 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  have hz : ⌈(49 / 12 : ℝ)⌉₊ = 5 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num at h
  rw [hy, hz] at h
  exact h

-- A genuinely fractional Y row still has the lower bound with an independent real Z budget.
example : (2 : ℝ) * ((7 / 2) * (7 / 2 + 1) * 6 / 2 - ((7 / 2) ^ 3 - 7 / 2) / 6) ≤
    (monomialSupport 2 7 4 6).card := by
  have h := card_monomialSupport_ceil_lower_bound 2 (7 / 2) 6 (by norm_num) (by norm_num)
  have hy : ⌈(7 / 2 : ℝ)⌉₊ = 4 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num at h ⊢
  rwa [hy] at h
