/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.HighestJetRefinement
public import Mathlib.Algebra.Field.ZMod

/-!
# Highest-jet execution regressions

Kernel computations include normalization, cancellation, index-zero exclusion, zero exponents,
lexicographic register updates and final output. Literal charges cover both machine phases.
-/

@[expose] public section

namespace MvPolynomial.HighestJetMachine

/-- A higher variable wins even when a lower variable has a much larger exponent. -/
example : runFuel 11 (.normalizing (.terms
    [(2, [(0, 100), (1, 20), (3, 2)])] []) : Configuration ℕ) =
    (.done (some (3, 2)), ⟨⟨0, 0, 15, 50, 15, 2⟩, 1⟩) := by decide +kernel

/-- The distinguished variable and zero exponents never produce an active jet. -/
example : runFuel 11 (.normalizing (.terms
    [(2, [(0, 100), (1, 0), (3, 0)])] []) : Configuration ℕ) =
    (.done none, ⟨⟨0, 0, 15, 50, 15, 2⟩, 1⟩) := by decide +kernel

/-- Different surviving powers of the same highest variable yield its maximum exponent. -/
example : runFuel 18 (.normalizing (.terms
    [(2, [(3, 1)]), (3, [(3, 7)])] []) : Configuration ℕ) =
    (.done (some (3, 7)), ⟨⟨0, 0, 28, 93, 12, 2⟩, 2⟩) := by decide +kernel

/-- A later lower exponent must not overwrite the maximum exponent register. -/
example : runFuel 18 (.normalizing (.terms
    [(3, [(3, 7)]), (2, [(3, 1)])] []) : Configuration ℕ) =
    (.done (some (3, 7)), ⟨⟨0, 0, 28, 93, 12, 2⟩, 2⟩) := by decide +kernel

/-- Cancellation of the syntactically highest jet exposes the lower, genuinely active jet. -/
example : runFuel 28 (.normalizing (.terms
    [(2, [(0, 50), (1, 2), (3, 0)]), (3, [(0, 0), (1, 0), (3, 4)]),
      (2, [(0, 0), (1, 0), (3, 4)])] []) : Configuration (ZMod 5)) =
    (.done (some (1, 2)), ⟨⟨1, 0, 49, 171, 25, 2⟩, 4⟩) := by decide +kernel

/-- Complete cancellation leaves no jet, although the input contains a positive high exponent. -/
example : runFuel 12 (.normalizing (.terms
    [(2, [(9, 4)]), (3, [(9, 4)])] []) : Configuration (ZMod 5)) =
    (.done none, ⟨⟨1, 0, 22, 67, 2, 2⟩, 3⟩) := by decide +kernel

/-- One step before output the exact maximum has been computed but not emitted. -/
example : runFuel 14 (.normalizing (.terms
    [(2, [(1, 1)]), (3, [(1, 1)])] []) : Configuration ℕ) =
    (.terms [] (some (1, 1)), ⟨⟨1, 0, 24, 78, 7, 1⟩, 3⟩) := by decide +kernel

/-- Empty input pays the two output boundaries and phase initialization. -/
example : runFuel 3 (.normalizing (.terms [] []) : Configuration ℕ) =
    (.done none, ⟨⟨0, 0, 4, 8, 0, 2⟩, 0⟩) := by decide +kernel

end MvPolynomial.HighestJetMachine
