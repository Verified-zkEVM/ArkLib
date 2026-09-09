/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterShiftMachine
/-!
# Closed center-shift canaries

Kernel computations check the sign of the translation, descending output order, retained leading
zeros, final return, and degree zero. Every cost includes the separate negation field.
-/

open ReedSolomon.HiddenDerivative.CenterShiftMachine

-- 3(X-2)² + 4(X-2) + 5 = 3X² - 8X + 9.
example : runFuel (⟨[3, 4, 5], 2, 2⟩ : Input ℤ) 46 .start =
    (.done (some [3, -8, 9]), ⟨⟨9, 9, 89, 285, 16, 5⟩, 0, 1⟩) := by decide

-- The preparation callee has emitted, but the final outer return is still pending.
example : runFuel (⟨[3, 4, 5], 2, 2⟩ : Input ℤ) 45 .start =
    (.prepare (.done (some [3, -8, 9])), ⟨⟨9, 9, 88, 283, 16, 4⟩, 0, 1⟩) := by decide

-- A leading zero remains a physical coefficient cell after shifting.
example : runFuel (⟨[0, 2, 3], 2, 2⟩ : Input ℤ) 46 .start =
    (.done (some [0, 2, -1]), ⟨⟨9, 9, 89, 285, 16, 5⟩, 0, 1⟩) := by decide

-- Degree zero has one coefficient; even the zero center incurs the explicit negation charge.
example : runFuel (⟨[7], 0, 0⟩ : Input ℤ) 18 .start =
    (.done (some [7]), ⟨⟨1, 1, 33, 93, 8, 3⟩, 0, 1⟩) := by decide
