/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.RowReductionMachine

/-!
# Concrete row-operation machine checks

Asymmetric signed rows fix arithmetic orientation and reversal order. The remaining cases
distinguish exhaustion, both length-mismatch directions, and successful empty rows with no
field arithmetic.
-/

@[expose] public section

namespace Matrix.RowReductionMachine

/-- Three distinct entries, with negative source and multiplier values. -/
example : runFuel (-2 : ℤ) 14 (.scan [2, 5, 11] [3, -2, 4] []) =
    (.done [-4, 9, 3], ⟨3, 3, 14, 62, 1⟩) := by decide

/-- Reversal is complete but emission is still pending one transition before termination. -/
example : runFuel (-2 : ℤ) 13 (.scan [2, 5, 11] [3, -2, 4] []) =
    (.reverse [] [-4, 9, 3], ⟨3, 3, 13, 60, 0⟩) := by decide

/-- A short source rejects after two arithmetic pairs, without reversing a partial output. -/
example : runFuel (-2 : ℤ) 7 (.scan [2, 5, 11] [3, -2] []) =
    (.rejected, ⟨2, 2, 7, 30, 1⟩) := by decide

/-- A short target follows the other rejection branch, even when no pair can be processed. -/
example : runFuel (2 : ℤ) 1 (.scan [] [7] []) =
    (.rejected, ⟨0, 0, 1, 2, 1⟩) := by decide

/-- Empty equal-length rows still initialize reversal and emit a successful result. -/
example : runFuel (2 : ℤ) 2 (.scan [] [] []) =
    (.done [], ⟨0, 0, 2, 5, 1⟩) := by decide

end Matrix.RowReductionMachine
