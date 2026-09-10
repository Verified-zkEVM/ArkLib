/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ColumnEliminationMachine

/-!
# Concrete checks for full-column elimination

Kernel reduction checks multirow order, unchanged head, explicit outer reversal and emission,
head validation with no targets, and rejection without a partial matrix.
-/

@[expose] public section

namespace Matrix.ColumnEliminationMachine

/-- Two targets include both a nontrivial inverse and an already-zero selected entry. -/
example : runFuel 1 55 (.begin ([[2, 2, 4], [3, 5, 2], [6, 0, 1]] : List (List ℚ))) =
    (.done [[2, 2, 4], [-2, 0, -8], [6, 0, 1]],
      ⟨⟨6, 8, 55, 231, 5⟩, 2, 2, 3, 9⟩) := by decide +kernel

/-- One less step leaves the outer emit pending, even though all output rows exist. -/
example : runFuel 1 54 (.begin ([[2, 2, 4], [3, 5, 2], [6, 0, 1]] : List (List ℚ))) =
    (.reverse [] [[2, 2, 4], [-2, 0, -8], [6, 0, 1]],
      ⟨⟨6, 8, 54, 229, 4⟩, 2, 2, 3, 9⟩) := by decide +kernel

/-- A head-only matrix still pays for pivot validation and outer construction. -/
example : runFuel 1 7 (.begin ([[2, 2, 4]] : List (List ℚ))) =
    (.done [[2, 2, 4]], ⟨⟨0, 0, 7, 25, 1⟩, 0, 0, 1, 3⟩) := by decide +kernel

/-- An empty tail does not allow an invalid zero head pivot to pass. -/
example : runFuel 1 4 (.begin ([[2, 0, 4]] : List (List ℚ))) =
    (.rejected, ⟨⟨0, 0, 4, 14, 1⟩, 0, 0, 1, 3⟩) := by decide +kernel

/-- Missing target entries abort without emitting the stored head as a partial matrix. -/
example : runFuel 1 8 (.begin ([[2, 2, 4], [3]] : List (List ℚ))) =
    (.rejected, ⟨⟨0, 0, 8, 34, 2⟩, 0, 0, 1, 5⟩) := by decide +kernel

/-- A length mismatch after one successful target still exposes no partial matrix. -/
example : (runFuel 1 100
    (.begin ([[2, 2, 4], [3, 5, 2], [3, 5]] : List (List ℚ)))).1 = .rejected := by
  decide +kernel

/-- Out-of-range head lookup rejects even with no target rows. -/
example : runFuel 4 5 (.begin ([[2, 2, 4]] : List (List ℚ))) =
    (.rejected, ⟨⟨0, 0, 5, 19, 1⟩, 0, 0, 0, 6⟩) := by decide +kernel

/-- Empty matrix input has its own immediate structural rejection. -/
example : runFuel 1 1 (.begin ([] : List (List ℚ))) =
    (.rejected, ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩) := by decide +kernel

end Matrix.ColumnEliminationMachine
