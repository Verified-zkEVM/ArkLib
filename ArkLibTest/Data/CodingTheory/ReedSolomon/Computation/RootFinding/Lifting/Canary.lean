/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Semantics
/-!
# Whole-vector regular lift execution

Two stages recover zero then one, update different physical positions, and emit the complete
quadratic candidate. Failure and zero-stage cases distinguish the loop's terminal branches.
-/

open ReedSolomon.HiddenDerivative.RegularLiftMachine

-- Q=Y₀-X², initial jet zero: stages k=1,2 recover gamma=0,1 and produce X².
example : runFuel (⟨[0, 0, 0], [(1, [(1, 1)]), (-1, [(0, 2)])], 0, 0⟩ : Input ℚ)
    2 3 1819 (.start [0, 1, 2]) =
      (.done (some [1, 0, 0]),
        ⟨⟨⟨186, 218, 10781, 25457, 139⟩, 26, 26, 50, 611⟩, 14⟩) := by decide +kernel

-- The completed vector is retained one step before the separately charged final output.
example : runFuel (⟨[0, 0, 0], [(1, [(1, 1)]), (-1, [(0, 2)])], 0, 0⟩ : Input ℚ)
    2 3 1818 (.start [0, 1, 2]) =
      (.emit (some [1, 0, 0]),
        ⟨⟨⟨186, 218, 10780, 25455, 138⟩, 26, 26, 50, 611⟩, 14⟩) := by decide +kernel

-- Q=X has zero slope and fails the direct stage instead of advancing a fabricated candidate.
example : runFuel (⟨[0, 0], [(1, [(0, 1)])], 0, 0⟩ : Input ℚ)
    1 2 1000 (.start [0, 1]) =
      (.done none, ⟨⟨⟨40, 40, 2647, 6230, 47⟩, 6, 7, 15, 140⟩, 5⟩) := by decide +kernel

-- Zero stages retain the initial physical vector but still charge initialization and emission.
example : runFuel (⟨[7], [], 0, 0⟩ : Input ℚ) 0 1 3 (.start [0]) =
    (.done (some [7]), ⟨⟨⟨0, 0, 3, 9, 1⟩, 0, 0, 0, 3⟩, 0⟩) := by decide
