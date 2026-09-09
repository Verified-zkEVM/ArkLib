/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetPreparationMachine
/-!
# Initial-jet preparation canaries

Kernel computations distinguish reversal, padding, exact capacity, overlong rejection, empty jets,
and the separately charged emission boundary. Cost vectors include scalar zero constants.
-/

open ReedSolomon.HiddenDerivative.JetPreparationMachine

example : runFuel 9 (.start 4 [3, 0, 2] : Configuration ℕ) =
    (.done (some [0, 0, 2, 0, 3]), ⟨⟨0, 0, 9, 45, 12, 1⟩, 2⟩) := by decide

example : runFuel 8 (.start 4 [3, 0, 2] : Configuration ℕ) =
    (.emit (some [0, 0, 2, 0, 3]), ⟨⟨0, 0, 8, 43, 12, 0⟩, 2⟩) := by decide

example : runFuel 7 (.start 2 [3, 0, 2] : Configuration ℕ) =
    (.done (some [2, 0, 3]), ⟨⟨0, 0, 7, 35, 8, 1⟩, 0⟩) := by decide

example : runFuel 6 (.start 1 [3, 4, 5] : Configuration ℕ) =
    (.done none, ⟨⟨0, 0, 5, 25, 6, 1⟩, 0⟩) := by decide

example : runFuel 5 (.start 0 [] : Configuration ℕ) =
    (.done (some [0]), ⟨⟨0, 0, 5, 16, 4, 1⟩, 1⟩) := by decide
