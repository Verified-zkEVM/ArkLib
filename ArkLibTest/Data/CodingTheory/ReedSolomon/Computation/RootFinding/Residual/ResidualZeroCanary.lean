/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualZeroMachine
/-!
# Closed residual-zero canaries

The materialized polynomial is `P(T)=T` and the sparse equation selects `Y₀`. Thus the supplied
points are also the sampled values. Exact costs distinguish a nontrivial all-zero scan, early
rejection after one or two tests, and the final emission boundary. All batch work remains charged.
-/

open ReedSolomon.HiddenDerivative.ResidualZeroMachine

example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 77 (.start [0, 0]) =
    (.done true, ⟨⟨8, 6, 250, 621, 20, 8⟩, 2⟩) := by decide +kernel

-- The third pair is not tested after rejection at the second value.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 112 (.start [0, 2, 0]) =
    (.done false, ⟨⟨12, 9, 368, 916, 30, 11⟩, 2⟩) := by decide +kernel

-- Rejecting at the first value saves exactly one scan transition and one equality.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 112 (.start [2, 0, 0]) =
    (.done false, ⟨⟨12, 9, 367, 912, 30, 11⟩, 1⟩) := by decide +kernel

-- One step before actual early completion, the Boolean has not been emitted.
example : runFuel (⟨[1, 0], [(1, [(1, 1)])], 3, 0⟩ : Input ℕ) 109 (.start [0, 2, 0]) =
    (.emit false, ⟨⟨12, 9, 367, 914, 30, 10⟩, 2⟩) := by decide +kernel

-- Empty samples still execute the empty batch, handoff, exhaustion branch, and final emission.
example : runFuel (⟨[], [], 3, 0⟩ : Input ℕ) 7 (.start []) =
    (.done true, ⟨⟨0, 0, 10, 21, 0, 2⟩, 0⟩) := by decide
