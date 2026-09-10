/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.PartialDerivativeRefinement
public import Mathlib.Algebra.Field.ZMod

/-!
# Sparse differentiation execution regressions

Literal kernel computations cover factor order, restoration, duplicate terms, absent variables,
zero exponents, zero coefficients, characteristic cancellation and the final output boundary.
-/

@[expose] public section

namespace MvPolynomial.PartialDerivativeMachine

/-- A selected factor in the middle is decremented without reordering the remaining variables.
Four scalar additions and two prefix/output reversals are included in the literal cost. -/
example : runFuel 1 23 (.terms
    [(2, [(5, 2), (1, 3), (7, 0)]), (3, [(1, 1)]), (4, [(2, 1)])] [] : Configuration ℕ) =
    (.done [(6, [(5, 2), (1, 2), (7, 0)]), (3, [(1, 0)])], ⟨⟨4, 0, 23, 95, 18, 3⟩, 2⟩) := by
  decide +kernel

/-- One step before completion the reversed term list is ready but has not been emitted. -/
example : runFuel 1 22 (.terms
    [(2, [(5, 2), (1, 3), (7, 0)]), (3, [(1, 1)]), (4, [(2, 1)])] [] : Configuration ℕ) =
    (.reverse [] [(6, [(5, 2), (1, 2), (7, 0)]), (3, [(1, 0)])],
      ⟨⟨4, 0, 22, 93, 18, 2⟩, 2⟩) := by decide +kernel

/-- Duplicate terms remain duplicate; no coefficient collection or normalization is hidden. -/
example : runFuel 0 16 (.terms [(2, [(0, 1)]), (2, [(0, 1)])] [] : Configuration ℕ) =
    (.done [(2, [(0, 0)]), (2, [(0, 0)])], ⟨⟨2, 0, 16, 63, 12, 3⟩, 2⟩) := by decide +kernel

/-- The selected exponent can vanish, with no scaling loop or scalar zero test. -/
example : runFuel 1 4 (.terms [(7, [(1, 0)])] [] : Configuration ℕ) =
    (.done [], ⟨⟨0, 0, 4, 11, 2, 1⟩, 0⟩) := by decide +kernel

/-- Missing variables require a full factor scan. -/
example : runFuel 2 6 (.terms [(3, [(0, 2), (1, 3)])] [] : Configuration ℕ) =
    (.done [], ⟨⟨0, 0, 6, 22, 2, 1⟩, 0⟩) := by decide +kernel

/-- Scaling zero still pays every repeated addition before the scalar test drops the term. -/
example : runFuel 1 9 (.terms [(0, [(1, 3)])] [] : Configuration ℕ) =
    (.done [], ⟨⟨3, 0, 9, 34, 10, 1⟩, 1⟩) := by decide +kernel

/-- Characteristic cancellation is discovered by actual repeated addition and a scalar test. -/
example : runFuel 0 11 (.terms [(2, [(0, 5)])] [] : Configuration (ZMod 5)) =
    (.done [], ⟨⟨5, 0, 11, 44, 14, 1⟩, 1⟩) := by decide +kernel

/-- Empty input still pays reversal initialization and final output. -/
example : runFuel 0 2 (.terms [] [] : Configuration ℕ) =
    (.done [], ⟨⟨0, 0, 2, 5, 0, 1⟩, 0⟩) := by decide +kernel

end MvPolynomial.PartialDerivativeMachine
