/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ForwardEchelonMachine

/-!
# Forward-echelon driver regression checks

These kernel computations exercise skipped columns, row movement, increasing pivot indices,
nontrivial RHS elimination, retained zero-coefficient rows and the final output boundary.
-/

@[expose] public section

namespace Matrix.ForwardEchelonMachine

/-- Column zero is skipped, a later row becomes pivot, and a contradictory residual is retained. -/
example : runFuel 180 (.loop 0 3
    ([([0, 0, 2], 4), ([0, 3, 6], 12), ([0, 0, 0], 5)] : List (Row ℚ)) []) =
    (.done [(1, ([0, 3, 6], 12)), (2, ([0, 0, 2], 4))] [([0, 0, 0], 5)],
      ⟨⟨12, 15, 453, 1348, 14⟩, 3, 3, 11, 55⟩) := by decide +kernel

/-- The final result is not emitted one step before exact completion. -/
example : runFuel 179 (.loop 0 3
    ([([0, 0, 2], 4), ([0, 3, 6], 12), ([0, 0, 0], 5)] : List (Row ℚ)) []) =
    (.reverse [] [(1, ([0, 3, 6], 12)), (2, ([0, 0, 2], 4))] [([0, 0, 0], 5)],
      ⟨⟨12, 15, 452, 1345, 13⟩, 3, 3, 11, 55⟩) := by decide +kernel

/-- A second pivot is computed after actual arithmetic changes both coefficients and RHS. -/
example : runFuel 82 (.loop 0 2 ([([1, 2], 3), ([2, 5], 7)] : List (Row ℚ)) []) =
    (.done [(0, ([1, 2], 3)), (1, ([0, 1], 1))] [],
      ⟨⟨3, 4, 193, 573, 9⟩, 1, 1, 5, 24⟩) := by decide +kernel

/-- Exhausting an all-zero coefficient matrix retains its nonzero RHS. -/
example : runFuel 21 (.loop 0 2 ([([0, 0], 7)] : List (Row ℚ)) []) =
    (.done [] [([0, 0], 7)], ⟨⟨0, 0, 36, 109, 3⟩, 0, 0, 2, 11⟩) := by decide +kernel

/-- Zero coefficient width emits rows without inspecting their RHS for consistency. -/
example : runFuel 2 (.loop 0 0 ([([], 7)] : List (Row ℚ)) []) =
    (.done [] [([], 7)], ⟨⟨0, 0, 2, 7, 1⟩, 0, 0, 0, 1⟩) := by decide +kernel

/-- Empty active input still executes the finite column scan and final output. -/
example : runFuel 12 (.loop 0 2 ([] : List (Row ℚ)) []) =
    (.done [] [], ⟨⟨0, 0, 18, 47, 3⟩, 0, 0, 0, 7⟩) := by decide +kernel

/-- A missing coefficient rejects through the delegated selection failure path. -/
example : runFuel 4 (.loop 0 1 ([([], 7)] : List (Row ℚ)) []) =
    (.rejected, ⟨⟨0, 0, 6, 18, 2⟩, 0, 0, 0, 2⟩) := by decide +kernel

/-- An impossible successful-empty selection return has an explicit rejection transition. -/
example : runFuel 1 (.select 0 0 [] (.done true []) : Configuration ℚ) =
    (.rejected, ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩) := by decide +kernel

end Matrix.ForwardEchelonMachine
