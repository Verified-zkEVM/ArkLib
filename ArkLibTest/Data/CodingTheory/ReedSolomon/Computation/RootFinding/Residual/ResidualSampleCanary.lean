/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSampleMachine
import Mathlib.Data.ZMod.Basic
/-!
# Closed residual sample machine canaries

Kernel computations check exact completion, insufficient fuel, empty inputs, and characteristic two.
-/

open ReedSolomon.HiddenDerivative.ResidualSampleMachine

-- P = 3T² + 4T + 5, center = 3, sample = 2, Q = X * Y₁ + Y₀: value 5 * 16 + 25 = 105.
example : runFuel
    (⟨[3, 4, 5], [(1, [(0, 1), (2, 1)]), (1, [(1, 1)])], 3, 2, 2⟩ : Input ℕ) 61 .start =
    (.done 105, ⟨12, 12, 117, 356, 26, 5⟩) := by decide

-- One fewer step leaves the scalar submachine complete, before the outer machine emits its result.
example : runFuel
    (⟨[3, 4, 5], [(1, [(0, 1), (2, 1)]), (1, [(1, 1)])], 3, 2, 2⟩ : Input ℕ) 60 .start =
    (.scalar [5, 25, 16, 3] (.done 105), ⟨12, 12, 116, 354, 26, 4⟩) := by decide

-- Empty polynomial and equation lists still account for initialization and output.
example : runFuel (⟨[], [], 3, 2, 0⟩ : Input ℕ) 11 .start =
    (.done 0, ⟨1, 0, 17, 42, 4, 3⟩) := by decide

-- The second Hasse derivative of T² remains one in characteristic two.
example : (runFuel
    (⟨[1, 0, 0], [(1, [(0, 1)]), (1, [(3, 1)])], 1, 1, 2⟩ : Input (ZMod 2))
    (fuel ⟨[1, 0, 0], [(1, [(0, 1)]), (1, [(3, 1)])], 1, 1, 2⟩) .start).1 = .done 1 := by decide
