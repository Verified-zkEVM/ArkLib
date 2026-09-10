/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.BackSubstitutionMachine

/-!
# Back-substitution execution regressions

Kernel computations check literal results and independently counted costs, including nonzero
supplied free coordinates, reverse pivot order, residual contradictions and output boundaries.
-/

@[expose] public section

namespace Matrix.BackSubstitutionMachine

/-- A free coordinate remains one while both initially nonzero pivot coordinates are corrected. -/
example : runFuel 39 (.check []
    [(0, ([2, 1, 0], 7)), (2, ([0, 0, 3], 9))] [5, 1, 8] : Configuration ℚ) =
    (.done [3, 1, 3], ⟨⟨10, 8, 69, 225, 3⟩, 2, 2, 2, 12⟩) := by decide +kernel

/-- One step short leaves the final vector ready but not emitted. -/
example : runFuel 38 (.check []
    [(0, ([2, 1, 0], 7)), (2, ([0, 0, 3], 9))] [5, 1, 8] : Configuration ℚ) =
    (.solve [] [3, 1, 3], ⟨⟨10, 8, 68, 224, 2⟩, 2, 2, 2, 12⟩) := by decide +kernel

/-- Solving the lower row first is necessary for this coupled system. -/
example : runFuel 34 (.check []
    [(0, ([1, 2], 3)), (1, ([0, 1], 1))] [9, 8] : Configuration ℚ) =
    (.done [1, 1], ⟨⟨8, 6, 59, 189, 3⟩, 2, 2, 2, 8⟩) := by decide +kernel

/-- A contradiction after a consistent residual stops before any pivot processing. -/
example : runFuel 2 (.check [([0, 0], 0), ([0, 0], 5)]
    [(0, ([1, 0], 3))] [9, 8] : Configuration ℚ) =
    (.inconsistent, ⟨⟨0, 0, 2, 6, 1⟩, 0, 0, 2, 0⟩) := by decide +kernel

/-- A consistent system with no pivots returns the entire supplied free vector. -/
example : runFuel 4 (.check [([0, 0], 0)] [] [9, 8] : Configuration ℚ) =
    (.done [9, 8], ⟨⟨0, 0, 4, 10, 1⟩, 0, 0, 1, 0⟩) := by decide +kernel

/-- Empty input still pays for residual completion, reversal completion and emission. -/
example : runFuel 3 (.check [] [] [] : Configuration ℚ) =
    (.done [], ⟨⟨0, 0, 3, 7, 1⟩, 0, 0, 0, 0⟩) := by decide +kernel

/-- Malformed row/vector lengths reject through the actual delegated transition. -/
example : runFuel 6 (.check [] [(0, ([1], 3))] [] : Configuration ℚ) =
    (.rejected, ⟨⟨0, 0, 7, 23, 2⟩, 0, 0, 0, 0⟩) := by decide +kernel

/-- One-row correction traverses and restores a nonempty prefix and inverts a nonunit pivot. -/
example : PivotSolveMachine.runFuel (F := ℚ) ([0, 0, 3], 9) 2 [5, 1, 8] 18
    (.dot [0, 0, 3] [5, 1, 8] 0)
    = (.done [5, 1, 3], ⟨⟨5, 4, 18, 78, 1⟩, 1, 1, 1, 10⟩) := by decide +kernel

end Matrix.BackSubstitutionMachine
