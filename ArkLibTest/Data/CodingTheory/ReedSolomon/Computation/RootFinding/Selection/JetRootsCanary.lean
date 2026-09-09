/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsSemantics
import Mathlib.Algebra.Field.ZMod
/-!
# All-jet enumeration and root collection boundaries

A permuted complete alphabet checks lexicographic tuple order and ordered success collection.
Positive padding, nonzero center and total rejection exercise the composed preparation/root path.
-/

open ReedSolomon.HiddenDerivative.JetRootsMachine

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- Nine length-two jets for Q=Y₁ yield all three constant roots in the supplied alphabet order.
example : runFuel (⟨[2, 0, 1], [(1, [(2, 1)])], 1, 1⟩ : Input (ZMod 3))
    1 2 1149 (.start [0, 1]) =
      (.done (some [[0, 2], [0, 0], [0, 1]]),
        ⟨⟨⟨120, 102, 5192, 12482, 132⟩, 0, 3, 12, 393⟩, 0⟩) := by decide +kernel

-- The collected list is ready one step before its separately charged tagged output.
example : runFuel (⟨[2, 0, 1], [(1, [(2, 1)])], 1, 1⟩ : Input (ZMod 3))
    1 2 1148 (.start [0, 1]) =
      (.emit (some [[0, 2], [0, 0], [0, 1]]),
        ⟨⟨⟨120, 102, 5191, 12480, 131⟩, 0, 3, 12, 393⟩, 0⟩) := by decide +kernel

-- Each length-one jet is padded; Q=Y₀-X at center one retains only the global polynomial X.
example : runFuel (⟨[2, 0, 1], [(1, [(1, 1)]), (-1, [(0, 1)])], 1, 0⟩ : Input (ZMod 3))
    1 2 5000 (.start [0, 1]) =
      (.done (some [[1, 0]]),
        ⟨⟨⟨169, 163, 13307, 30286, 181⟩, 21, 22, 49, 636⟩, 18⟩) := by decide +kernel

-- The generic machine also supports partial alphabets: all rejected candidates emit an empty list.
example : runFuel (⟨[0], [(1, [(1, 1)]), (-1, [(0, 2)])], 0, 0⟩ : Input ℚ)
    1 3 3000 (.start [0, 1, 2]) =
      (.done (some []), ⟨⟨⟨102, 118, 7726, 17617, 86⟩, 13, 13, 27, 366⟩, 8⟩) := by decide +kernel
