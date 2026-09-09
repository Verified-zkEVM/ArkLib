/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsSemantics
import Mathlib.Algebra.Field.ZMod
/-!
# Actual stage traversal and immutable guard contexts

A multi-stage chain retains distinct contexts for the same polynomial. The terminal and missing
successor boundaries check graceful completion and failure with exact primitive charges.
-/

open ReedSolomon.HiddenDerivative.StageRootsMachine

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The actual chain Y₀ → 1 returns zero at all centers, with the literal successor equation.
example : runFuel (⟨[0, 1, 2], [(1, [(0, 0), (1, 1)])], 0⟩ : Input (ZMod 3))
    0 1 10000 (.start [0]) =
      (.done (some [
        ⟨⟨⟨[(1, [(0, 0), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 0), (1, 0)])]⟩, 0, [0]⟩,
        ⟨⟨⟨[(1, [(0, 0), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 0), (1, 0)])]⟩, 1, [0]⟩,
        ⟨⟨⟨[(1, [(0, 0), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 0), (1, 0)])]⟩, 2, [0]⟩]),
        ⟨⟨⟨31, 21, 4138, 9552, 103⟩, 0, 3, 12, 269⟩, 0⟩) := by decide +kernel

-- Both Y₀² and 2Y₀ emit zero; the second context retains the earlier raw equation exactly.
example : runFuel (⟨[0], [(1, [(0, 0), (1, 2)])], 0⟩ : Input ℚ)
    0 1 10000 (.start [0]) =
      (.done (some [
        ⟨⟨⟨[(1, [(0, 0), (1, 2)])], some (1, 2)⟩, [], [(2, [(0, 0), (1, 1)])]⟩, 0, [0]⟩,
        ⟨⟨⟨[(2, [(0, 0), (1, 1)])], some (1, 1)⟩, [[(1, [(0, 0), (1, 2)])]],
          [(2, [(0, 0), (1, 0)])]⟩, 0, [0]⟩]),
        ⟨⟨⟨11, 7, 1430, 3421, 48⟩, 0, 2, 7, 124⟩, 0⟩) := by decide +kernel

-- A terminal-only chain is traversed and emits no candidate records.
example : runFuel (⟨[0], [(1, [(0, 0), (1, 0)])], 0⟩ : Input ℚ)
    0 1 1000 (.start [0]) =
      (.done (some []), ⟨⟨⟨0, 0, 49, 131, 6⟩, 0, 0, 1, 10⟩, 0⟩) := by decide +kernel

-- An externally suspended malformed active stage cannot invent a successor separant.
example : runFuel (⟨[0], [], 0⟩ : Input ℚ) 0 1 5
    (.scan [⟨[(1, [(1, 1)])], some (1, 1)⟩] [] [] [0]) =
      (.done none, ⟨⟨⟨0, 0, 3, 14, 1⟩, 0, 0, 0, 2⟩, 0⟩) := by decide +kernel

-- The first scan transition separately materializes the reversed earlier-equation prefix cell.
example : runFuel (⟨[0], [], 0⟩ : Input ℚ) 0 1 1
    (.scan [⟨[(1, [(1, 1)])], some (1, 1)⟩] [] [] [0]) =
      (.select ⟨[(1, [(1, 1)])], some (1, 1)⟩ [] [] [[(1, [(1, 1)])]] [] [0],
        ⟨⟨⟨0, 0, 1, 8, 0⟩, 0, 0, 0, 0⟩, 0⟩) := by decide +kernel

-- The active order drops from one to zero; higher zero-exponent factors remain in raw terms.
example : runFuel (⟨[0], [(1, [(0, 0), (1, 1), (2, 1)])], 1⟩ : Input ℚ)
    1 2 10000 (.start [0, 1]) =
      (.done (some [
        ⟨⟨⟨[(1, [(0, 0), (1, 1), (2, 1)])], some (2, 1)⟩, [],
          [(1, [(0, 0), (1, 1), (2, 0)])]⟩, 0, [0, 0]⟩,
        ⟨⟨⟨[(1, [(0, 0), (1, 1), (2, 0)])], some (1, 1)⟩,
          [[(1, [(0, 0), (1, 1), (2, 1)])]],
          [(1, [(0, 0), (1, 0), (2, 0)])]⟩, 0, [0, 0]⟩]),
        ⟨⟨⟨71, 67, 7529, 16962, 105⟩, 7, 9, 24, 385⟩, 6⟩) := by decide +kernel
