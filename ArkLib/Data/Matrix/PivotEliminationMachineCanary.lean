/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotEliminationMachine

/-!
# Concrete checks for composed pivot elimination

These runs fix indexed lookup, signed factor arithmetic, delegated row/reversal costs and the
outer return event. All three rejection mechanisms are exercised separately.
-/

@[expose] public section

namespace Matrix.PivotEliminationMachine

/-- Column one selects pivot `2` and entry `5`, exercising a nontrivial field inverse. -/
example : runFuel 21 (.lookup ([2, 2, 4] : List ℚ) [3, 5, 2] [2, 2, 4] [3, 5, 2] 1) =
    (.done [-2, 0, -8], ⟨⟨3, 4, 21, 85, 2⟩, 1, 1, 1, 3⟩) := by decide +kernel

/-- The inner result exists one transition before its charged outer return. -/
example : runFuel 20 (.lookup ([2, 2, 4] : List ℚ) [3, 5, 2] [2, 2, 4] [3, 5, 2] 1) =
    (.row (-5 / 2) (.done [-2, 0, -8]), ⟨⟨3, 4, 20, 84, 1⟩, 1, 1, 1, 3⟩) := by decide +kernel

/-- Zero pivot rejects without inverse or delegated field arithmetic. -/
example : runFuel 3 (.lookup ([2, 0, 4] : List ℚ) [3, 5, 2] [2, 0, 4] [3, 5, 2] 1) =
    (.rejected, ⟨⟨0, 0, 3, 12, 1⟩, 0, 0, 1, 3⟩) := by decide +kernel

/-- Out-of-range lookup pays for all traversed cells and never supplies a default pivot. -/
example : runFuel 4 (.lookup ([2, 1, 4] : List ℚ) [3, 5, 2] [2, 1, 4] [3, 5, 2] 4) =
    (.rejected, ⟨⟨0, 0, 4, 20, 1⟩, 0, 0, 0, 6⟩) := by decide +kernel

/-- Valid selected entries do not hide a later length mismatch in the delegated row scan. -/
example : runFuel 10 (.lookup ([2, 1] : List ℚ) [3] [2, 1] [3] 0) =
    (.rejected, ⟨⟨1, 2, 10, 33, 2⟩, 1, 1, 1, 1⟩) := by decide +kernel

end Matrix.PivotEliminationMachine
