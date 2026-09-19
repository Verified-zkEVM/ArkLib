/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationSupport

/-! Acceptance checks for the BCHKS25 integer interpolation support. -/

open Polynomial.SymbolicInterpolation

-- Unequal X and Z budgets detect exchanging the nested polynomial axes.
example : ⟨0, (7, 1)⟩ ∈ monomialSupport 2 9 4 6 := by decide

example : ⟨0, (1, 7)⟩ ∉ monomialSupport 2 9 4 6 := by decide

-- A high Y exponent reduces both the X and Z budgets.
example : ⟨3, (2, 2)⟩ ∈ monomialSupport 2 9 4 6 := by decide

example : ⟨3, (3, 2)⟩ ∉ monomialSupport 2 9 4 6 := by decide

example : (monomialSupport 2 9 4 6).card = 118 := by decide

example : (constraintSupport 3 6).card = 32 := by decide

-- Small and zero budgets remain well-defined even outside the closed-form regime.
example : (constraintSupport 3 1).card = 3 := by decide

example : (monomialSupport 2 0 4 6).card = 0 := by decide
