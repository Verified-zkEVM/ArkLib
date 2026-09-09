/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.RegularRootSemantics
/-!
# Accepted-root pipeline boundaries

A nonzero center distinguishes the local lifted square from the emitted global square. A locally
valid prefix with a nonzero full residual is rejected, and failed lifting never enters checking.
-/

open ReedSolomon.HiddenDerivative.RegularRootMachine

-- Q=Y₀-X², center two and jet four: local T²+4T+4 becomes global X² after checking.
example : runFuel (⟨[0, 0, 4], [(1, [(1, 1)]), (-1, [(0, 2)])], 2, 0⟩ : Input ℚ)
    2 3 2018 (.start [0, 1, 2]) =
      (.done (some [1, 0, 0]),
        ⟨⟨⟨213, 245, 13402, 31069, 156⟩, 26, 27, 53, 675⟩, 14⟩) := by decide +kernel

-- The final translated vector is retained one step before charged tagged emission.
example : runFuel (⟨[0, 0, 4], [(1, [(1, 1)]), (-1, [(0, 2)])], 2, 0⟩ : Input ℚ)
    2 3 2017 (.start [0, 1, 2]) =
      (.emit (some [1, 0, 0]),
        ⟨⟨⟨213, 245, 13401, 31067, 155⟩, 26, 27, 53, 675⟩, 14⟩) := by decide +kernel

-- At ambient degree one, the locally valid zero prefix leaves residual -T² and is rejected.
-- No center negation/translation occurs on this branch.
example : runFuel (⟨[0, 0], [(1, [(1, 1)]), (-1, [(0, 2)])], 0, 0⟩ : Input ℚ)
    1 3 3000 (.start [0, 1, 2]) =
      (.done none, ⟨⟨⟨102, 118, 6640, 15380, 82⟩, 13, 13, 27, 351⟩, 7⟩) := by decide +kernel

-- A failed direct stage bypasses the final residual and translation callees.
example : runFuel (⟨[0, 0], [(1, [(0, 1)])], 0, 0⟩ : Input ℚ)
    1 2 2000 (.start [0, 1]) =
      (.done none, ⟨⟨⟨40, 40, 3119, 7175, 48⟩, 6, 7, 15, 140⟩, 5⟩) := by decide +kernel
