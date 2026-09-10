/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.VandermondeMachine

/-!
# Augmented Vandermonde construction canaries

Distinct points and RHS entries expose ordering mistakes. Boundary runs check empty coefficient
rows, empty samples and the separately charged final output.
-/

@[expose] public section

namespace Matrix.VandermondeMachine

/-- Both row and coefficient reversals preserve the intended ascending-power order. -/
example : runFuel 2 28 (.start [(2, 7), (3, 11)] : Configuration ℕ) =
    (.done [([1, 2], 7), ([1, 3], 11)], ⟨⟨0, 4, 28, 115, 1⟩, 0, 0, 0, 10⟩) := by decide

/-- The completed rows still await a separately charged output event. -/
example : runFuel 2 27 (.start [(2, 7), (3, 11)] : Configuration ℕ) =
    (.emit [([1, 2], 7), ([1, 3], 11)], ⟨⟨0, 4, 27, 114, 0⟩, 0, 0, 0, 10⟩) := by decide

/-- Zero columns preserve both samples as augmented rows with empty coefficients. -/
example : runFuel 0 16 (.start [(2, 7), (3, 11)] : Configuration ℕ) =
    (.done [([], 7), ([], 11)], ⟨⟨0, 0, 16, 63, 1⟩, 0, 0, 0, 2⟩) := by decide

/-- Empty input does no power work but still initializes and emits the empty matrix. -/
example : runFuel 7 4 (.start [] : Configuration ℕ) =
    (.done [], ⟨⟨0, 0, 4, 9, 1⟩, 0, 0, 0, 0⟩) := by decide

end Matrix.VandermondeMachine
