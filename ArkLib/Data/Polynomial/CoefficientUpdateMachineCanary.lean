/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.CoefficientUpdateMachine

/-!
# Descending coefficient update canaries

Kernel computations distinguish prefix restoration, suffix preservation, exact emission, zero
increments with leading zeros, and rejection at and beyond the available input.
-/

@[expose] public section

open Polynomial.CoefficientUpdateMachine

-- Two copied prefix cells return in order; the untouched suffix remains intact.
example : runFuel 7 13 (.start [0, 3, 4, 5] 2 : Configuration ℕ) =
    (.done (some [0, 3, 11, 5]), ⟨1, 0, 9, 47, 5, 1⟩) := by decide

-- The result exists one step before completion, but emission has not yet been charged.
example : runFuel 7 8 (.start [0, 3, 4, 5] 2 : Configuration ℕ) =
    (.emit (some [0, 3, 11, 5]), ⟨1, 0, 8, 45, 5, 0⟩) := by decide

-- A zero increment still performs one addition and preserves the leading zero and physical length.
example : runFuel 0 9 (.start [0, 2] 0 : Configuration ℕ) =
    (.done (some [0, 2]), ⟨1, 0, 5, 19, 1, 1⟩) := by decide

-- The index equal to the length rejects without updating or emitting a truncated prefix.
example : runFuel 7 9 (.start [3, 4] 2 : Configuration ℕ) =
    (.done none, ⟨0, 0, 5, 25, 4, 1⟩) := by decide

-- Empty input rejects even a large index without decrementing it or performing an addition.
example : runFuel 7 5 (.start [] 100 : Configuration ℕ) =
    (.done none, ⟨0, 0, 3, 9, 0, 1⟩) := by decide
