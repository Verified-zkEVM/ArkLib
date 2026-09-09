/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualWitnessSemantics
/-!
# Ordered residual-search regressions

The equation selects `Y₀` and the represented polynomial is `T`, so sampled points equal sampled
values. Full batch work, the first nonzero point, early scan exit and tagged emission are checked
by kernel reduction, without an assumed evaluator or witness predicate.
-/

open ReedSolomon.HiddenDerivative.ResidualWitnessMachine

-- All-zero samples return no witness, even when points repeat.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 77 (.start [0, 0]) =
    (.done none, ⟨⟨8, 6, 250, 622, 20, 8⟩, 2⟩) := by decide +kernel

-- Two nonzero choices must return the earlier point, not the last one.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 112 (.start [0, 2, 3]) =
    (.done (some 2), ⟨⟨12, 9, 368, 917, 30, 11⟩, 2⟩) := by decide +kernel

-- Selecting the first value saves a comparison but does not discard any batch charge.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 112 (.start [2, 0, 0]) =
    (.done (some 2), ⟨⟨12, 9, 367, 913, 30, 11⟩, 1⟩) := by decide +kernel

-- The selected witness exists internally one transition before charged emission.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 109 (.start [0, 2, 3]) =
    (.emit (some 2), ⟨⟨12, 9, 367, 914, 30, 10⟩, 2⟩) := by decide +kernel

-- Empty samples still execute the empty batch, handoff and final tagged emission.
example : runFuel (⟨[], [], 3, 0⟩ : Input ℕ) 7 (.start []) =
    (.done none, ⟨⟨0, 0, 10, 22, 0, 2⟩, 0⟩) := by decide +kernel

-- Sample coordinates, not the distinct nonzero values attached to them, are emitted.
example : runFuel (⟨[], [], 0, 0⟩ : Input ℕ) 3 (.scan [(7, 0), (8, 9), (10, 1)]) =
    (.done (some 8), ⟨⟨0, 0, 3, 11, 0, 1⟩, 2⟩) := by decide +kernel
