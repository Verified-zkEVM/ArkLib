/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.DenseNormalizeRefinement
public import Mathlib.Algebra.Field.ZMod

/-!
# Aggregation execution regressions

Literal kernel computations cover cancellation, exponent and variable comparisons, unequal
key lengths, prefix restoration and the output boundary. Cost literals count each primitive.
-/

@[expose] public section

namespace MvPolynomial.DenseNormalizeMachine

/-- Equal dense keys add their coefficients after scanning the exponent entry. -/
example : runFuel 10 (.terms [(2, [(0, 1)]), (3, [(0, 1)])] [] : Configuration ℕ) =
    (.done [(5, [(0, 1)])], ⟨⟨1, 0, 10, 45, 2, 1⟩, 3⟩) := by decide +kernel

/-- Characteristic cancellation removes the entire key, including its syntactic variable. -/
example : runFuel 10 (.terms [(2, [(9, 4)]), (3, [(9, 4)])] [] : Configuration (ZMod 5)) =
    (.done [], ⟨⟨1, 0, 10, 43, 2, 1⟩, 3⟩) := by decide +kernel

/-- Different exponents stay distinct, and updating the second key restores the first. -/
example : runFuel 19 (.terms
    [(2, [(0, 1)]), (3, [(0, 2)]), (4, [(0, 2)])] [] : Configuration ℕ) =
    (.done [(2, [(0, 1)]), (7, [(0, 2)])], ⟨⟨1, 0, 19, 96, 6, 1⟩, 4⟩) := by decide +kernel

/-- Different variables with identical exponents must not be aggregated. -/
example : runFuel 10 (.terms [(2, [(0, 1)]), (3, [(1, 1)])] [] : Configuration ℕ) =
    (.done [(2, [(0, 1)]), (3, [(1, 1)])], ⟨⟨0, 0, 10, 47, 2, 1⟩, 2⟩) := by decide +kernel

/-- A shorter key remains distinct even when the extra exponent is zero. This input does
not satisfy a shared dense layout, although unconditional polynomial preservation still holds. -/
example : runFuel 10 (.terms [(2, [(0, 0)]), (3, [])] [] : Configuration ℕ) =
    (.done [(2, [(0, 0)]), (3, [])], ⟨⟨0, 0, 10, 46, 0, 1⟩, 2⟩) := by decide +kernel

/-- The opposite unequal-length comparison also restores the previous key. -/
example : runFuel 10 (.terms [(2, []), (3, [(0, 0)])] [] : Configuration ℕ) =
    (.done [(2, []), (3, [(0, 0)])], ⟨⟨0, 0, 10, 46, 0, 1⟩, 2⟩) := by decide +kernel

/-- A zero input coefficient requires no key search. -/
example : runFuel 2 (.terms [(0, [(100, 1000)])] [] : Configuration ℕ) =
    (.done [], ⟨⟨0, 0, 2, 4, 0, 1⟩, 1⟩) := by decide +kernel

/-- One step before completion the aggregate has not yet been emitted. -/
example : runFuel 9 (.terms [(2, [(0, 1)]), (3, [(0, 1)])] [] : Configuration ℕ) =
    (.terms [] [(5, [(0, 1)])], ⟨⟨1, 0, 9, 43, 2, 0⟩, 3⟩) := by decide +kernel

/-- Empty input still pays for final output. -/
example : runFuel 1 (.terms [] [] : Configuration ℕ) =
    (.done [], ⟨⟨0, 0, 1, 2, 0, 1⟩, 0⟩) := by decide +kernel

end MvPolynomial.DenseNormalizeMachine
