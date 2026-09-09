/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterRootsSemantics
import Mathlib.Algebra.Field.ZMod
/-!
# Center collection boundaries

Permuted centers and jets preserve both orders. The same global polynomial is retained at every
center, exercising the separate pair/cell allocations and the subsequent explicit reversal.
-/

open ReedSolomon.HiddenDerivative.CenterRootsMachine

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- Q=Y₁ retains each constant at all three centers in supplied center/jet order.
example : runFuel (⟨[2, 0, 1], [(1, [(2, 1)])], 1⟩ : Input (ZMod 3))
    1 2 3487 (.start [0, 1]) =
      (.done (some [(2, [0, 2]), (2, [0, 0]), (2, [0, 1]),
        (0, [0, 2]), (0, [0, 0]), (0, [0, 1]), (1, [0, 2]), (1, [0, 0]), (1, [0, 1])]),
        ⟨⟨⟨360, 306, 19063, 44530, 397⟩, 0, 9, 36, 1179⟩, 0⟩) := by decide +kernel

-- One fewer transition leaves the ordered records ready for separately charged emission.
example : runFuel (⟨[2, 0, 1], [(1, [(2, 1)])], 1⟩ : Input (ZMod 3))
    1 2 3486 (.start [0, 1]) =
      (.emit (some [(2, [0, 2]), (2, [0, 0]), (2, [0, 1]),
        (0, [0, 2]), (0, [0, 0]), (0, [0, 1]), (1, [0, 2]), (1, [0, 0]), (1, [0, 1])]),
        ⟨⟨⟨360, 306, 19062, 44528, 396⟩, 0, 9, 36, 1179⟩, 0⟩) := by decide +kernel

-- Padded length-one jets recover the global X vector at every center, retaining duplicates.
example : runFuel (⟨[2, 0, 1], [(1, [(1, 1)]), (-1, [(0, 1)])], 0⟩ : Input (ZMod 3))
    1 2 15000 (.start [0, 1]) =
      (.done (some [(2, [1, 0]), (0, [1, 0]), (1, [1, 0])]),
        ⟨⟨⟨507, 489, 45652, 102370, 544⟩, 63, 66, 147, 1908⟩, 54⟩) := by decide +kernel

-- A partial alphabet with no successful degree-one candidate yields an empty record list.
example : runFuel (⟨[0], [(1, [(1, 1)]), (-1, [(0, 2)])], 0⟩ : Input ℚ)
    1 3 3000 (.start [0, 1, 2]) =
      (.done (some []), ⟨⟨⟨102, 118, 8789, 19751, 87⟩, 13, 13, 27, 366⟩, 8⟩) := by decide +kernel
