/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotSelectionMachine

/-!
# Pivot selection regression checks

Distinct RHS values track row pairing through movement. Checks cover restoration order, output
boundaries, already-selected pivots, all-zero columns, empty matrices and malformed rows.
-/

@[expose] public section

namespace Matrix.PivotSelectionMachine

/-- The third row moves to the head; earlier rows and the untouched tail retain their order. -/
example : runFuel 1 16 (.scan
    ([([9, 0], 11), ([8, 0], 12), ([7, 3], 13), ([6, 4], 14)] : List (Row ℚ)) []) =
    (.done true [([7, 3], 13), ([9, 0], 11), ([8, 0], 12), ([6, 4], 14)],
      ⟨⟨0, 0, 16, 72, 1⟩, 0, 0, 3, 9⟩) := by decide +kernel

/-- Materialization does not bypass the final charged output event. -/
example : runFuel 1 15 (.scan
    ([([9, 0], 11), ([8, 0], 12), ([7, 3], 13), ([6, 4], 14)] : List (Row ℚ)) []) =
    (.emit true [([7, 3], 13), ([9, 0], 11), ([8, 0], 12), ([6, 4], 14)],
      ⟨⟨0, 0, 15, 71, 0⟩, 0, 0, 3, 9⟩) := by decide +kernel

/-- An all-zero selected column restores both rows and their nonzero RHS entries. -/
example : runFuel 1 13 (.scan ([([9, 0], 11), ([8, 0], 12)] : List (Row ℚ)) []) =
    (.done false [([9, 0], 11), ([8, 0], 12)],
      ⟨⟨0, 0, 13, 53, 1⟩, 0, 0, 2, 6⟩) := by decide +kernel

/-- A nonzero head needs no prefix traversal but still pays for head construction. -/
example : runFuel 0 5 (.scan ([([2], 7)] : List (Row ℚ)) []) =
    (.done true [([2], 7)], ⟨⟨0, 0, 5, 20, 1⟩, 0, 0, 1, 1⟩) := by decide +kernel

/-- A missing entry after a valid zero prefix rejects without returning the saved prefix. -/
example : runFuel 1 7 (.scan ([([9, 0], 11), ([8], 12)] : List (Row ℚ)) []) =
    (.rejected, ⟨⟨0, 0, 7, 31, 1⟩, 0, 0, 1, 5⟩) := by decide +kernel

/-- Empty input has a vacuous all-zero column and still emits a tagged result. -/
example : runFuel 7 3 (.scan ([] : List (Row ℚ)) []) =
    (.done false [], ⟨⟨0, 0, 3, 5, 1⟩, 0, 0, 0, 0⟩) := by decide +kernel

end Matrix.PivotSelectionMachine
