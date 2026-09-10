/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.DegreeTruncationSemantics

/-!
# Degree truncation boundaries

The vectors distinguish checked zero removal from unconditional truncation, and the exact
charges distinguish final emission from merely reaching its payload. Dimension zero accepts
the zero polynomial as an empty coefficient vector.
-/

@[expose] public section

namespace Polynomial.DegreeTruncationMachine

example : runFuel 5 3 5 (.start [0, 0, 2, 3, 4] : Configuration ℕ) =
    (.done (some [2, 3, 4]), ⟨5, 14, 6, 2, 1⟩) := by decide

example : runFuel 5 3 4 (.start [0, 0, 2, 3, 4] : Configuration ℕ) =
    (.emit (some [2, 3, 4]), ⟨4, 13, 6, 2, 0⟩) := by decide

example : runFuel 5 3 5 (.start [0, 1, 2, 3, 4] : Configuration ℕ) =
    (.done none, ⟨4, 12, 5, 2, 1⟩) := by decide

example : runFuel 2 0 5 (.start [0, 0] : Configuration ℕ) =
    (.done (some []), ⟨5, 14, 6, 2, 1⟩) := by decide

end Polynomial.DegreeTruncationMachine
