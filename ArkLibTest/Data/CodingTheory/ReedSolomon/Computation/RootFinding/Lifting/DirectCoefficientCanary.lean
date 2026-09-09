/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectCoefficientRefinement
/-!
# Direct coefficient execution boundaries

Nonzero center, a leading zero, an interior candidate update and a nonunit slope distinguish
indexing, recovery, subtraction and division. The zero-slope case performs no final inversion.
-/

open ReedSolomon.HiddenDerivative.DirectCoefficientMachine

-- P=3T+2, Q=X+2Y₀, center two, k=1: beta seven and slope two give -7/2.
example : runFuel (⟨[0, 3, 2], [(1, [(0, 1)]), (2, [(1, 1)])], 2, 0⟩ : Input ℚ)
    3 3 1 893 (.start [0, 1, 2]) =
      (.done (some (-7 / 2)), ⟨⟨⟨92, 103, 4440, 10786, 68⟩, 13, 13, 25, 284⟩, 7⟩) := by
  decide +kernel

-- The scalar payload is ready one step before its separately charged tagged emission.
example : runFuel (⟨[0, 3, 2], [(1, [(0, 1)]), (2, [(1, 1)])], 2, 0⟩ : Input ℚ)
    3 3 1 892 (.start [0, 1, 2]) =
      (.emit (some (-7 / 2)), ⟨⟨⟨92, 103, 4439, 10784, 67⟩, 13, 13, 25, 284⟩, 7⟩) := by
  decide +kernel

-- Q=X is unaffected by the candidate update: slope zero emits none, with no quotient inverse.
example : runFuel (⟨[0, 3, 2], [(1, [(0, 1)])], 2, 0⟩ : Input ℚ)
    3 3 1 1000 (.start [0, 1, 2]) =
      (.done none, ⟨⟨⟨86, 96, 4186, 10199, 68⟩, 12, 13, 25, 248⟩, 7⟩) := by decide +kernel

-- Exhausting a requested-coefficient cursor rejects instead of substituting a zero coefficient.
example : runFuel (⟨[], [], 0, 0⟩ : Input ℚ) 0 0 1 2 (.lookup none [] 1 []) =
    (.done none, ⟨⟨⟨0, 0, 2, 4, 1⟩, 0, 0, 0, 0⟩, 0⟩) := by decide
