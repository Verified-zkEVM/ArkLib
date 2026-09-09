/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Semantics
/-!
# Executed coefficient recovery boundaries

Kernel computations recover a nonconstant residual at a nonzero center, check the separately
charged final emission, and expose the one-cell zero-seed allocation transition.
-/

open ReedSolomon.HiddenDerivative.ResidualCoefficientMachine

-- P=3 and Q=X+Y₀ at center two produce residual 5+T, recovered in ascending order.
example : runFuel (⟨[3], [(1, [(0, 1)]), (1, [(1, 1)])], 2, 0⟩ : Input ℚ)
    2 228 (.start [0, 1]) =
      (.done (some [5, 1]), ⟨⟨⟨19, 20, 874, 2200, 22⟩, 3, 3, 7, 75⟩, 2⟩) := by decide +kernel

-- One step short retains the payload; the final tagged output has not been charged.
example : runFuel (⟨[3], [(1, [(0, 1)]), (1, [(1, 1)])], 2, 0⟩ : Input ℚ)
    2 227 (.start [0, 1]) =
      (.emit (some [5, 1]), ⟨⟨⟨19, 20, 873, 2198, 21⟩, 3, 3, 7, 75⟩, 2⟩) := by decide +kernel

-- A seed cell is materialized separately, with a scalar constant and natural counter work.
example : step (⟨[], [], 0, 0⟩ : Input ℚ) 2 (.initialize [] [] 2 []) =
    some (.initialize [] [] 1 [0], ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 2⟩, 1⟩) := by decide

-- Width zero still executes both callees and all handoffs, without allocating a scalar seed.
example : runFuel (⟨[], [], 0, 0⟩ : Input ℚ) 0 100 (.start []) =
    (.done (some []), ⟨⟨⟨0, 0, 46, 110, 6⟩, 0, 0, 0, 2⟩, 0⟩) := by decide +kernel
