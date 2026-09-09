/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSystemMachine
/-!
# Residual-system composition boundaries

A nonzero center affects the sampled independent variable. Both point/value pairs become matrix
rows and undergo elimination; the final emitted equations have the expected coefficients and RHS.
The one-short execution retains the completed callee result rather than emitting it for free.
-/

namespace ReedSolomon.HiddenDerivative.ResidualSystemMachine

-- P=3 and Q=X+Y₀ at center two give residual 5+T, sampled at zero and one.
example : runFuel (⟨[3], [(1, [(0, 1)]), (1, [(1, 1)])], 2, 0⟩ : Input ℚ)
    2 187 (.start [0, 1]) =
      (.done [(0, ([1, 0], 5)), (1, ([0, 1], 1))] [],
        ⟨⟨11, 14, 587, 1543, 18⟩, 1, 1, 5, 62⟩) := by decide +kernel

-- The final outer emission is separately charged, after all three callees finish.
example : runFuel (⟨[3], [(1, [(0, 1)]), (1, [(1, 1)])], 2, 0⟩ : Input ℚ)
    2 186 (.start [0, 1]) =
      (.echelon (.done [(0, ([1, 0], 5)), (1, ([0, 1], 1))] []),
        ⟨⟨11, 14, 586, 1540, 17⟩, 1, 1, 5, 62⟩) := by decide +kernel

-- Empty samples and zero columns still execute every handoff and output event.
example : runFuel (⟨[], [], 0, 0⟩ : Input ℚ) 0 13 (.start []) =
    (.done [] [], ⟨⟨0, 0, 22, 55, 4⟩, 0, 0, 0, 1⟩) := by decide +kernel

end ReedSolomon.HiddenDerivative.ResidualSystemMachine
