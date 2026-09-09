/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualBatchMachine
/-!
# Closed residual batch canaries

Exact kernel computations check ordered point-value pairs, repeated points, nonzero center and
jet order, the last emission boundary, and empty input.
-/

open ReedSolomon.HiddenDerivative.ResidualBatchMachine

-- P = 3T² + 4T + 5 and Q = X * Y₁ + Y₀, centered at three with jet order two.
-- Values at points two and one are 105 and 52; repeated points remain repeated.
example : runFuel
    (⟨[3, 4, 5], [(1, [(0, 1), (2, 1)]), (1, [(1, 1)])], 3, 2⟩ : Input ℕ)
    204 (.start [2, 1, 2]) =
      (.done [(2, 105), (1, 52), (2, 105)], ⟨36, 36, 555, 1522, 78, 16⟩) := by decide +kernel

-- The ordered pairs are ready one step before the separately charged emission.
example : runFuel
    (⟨[3, 4, 5], [(1, [(0, 1), (2, 1)]), (1, [(1, 1)])], 3, 2⟩ : Input ℕ)
    203 (.start [2, 1, 2]) =
      (.reverse [] [(2, 105), (1, 52), (2, 105)], ⟨36, 36, 554, 1520, 78, 15⟩) := by decide +kernel

-- Empty batches perform no sample calls but still initialize, start reversal, and emit.
example : runFuel (⟨[], [], 3, 2⟩ : Input ℕ) 3 (.start []) =
    (.done [], ⟨0, 0, 3, 7, 0, 1⟩) := by decide
