/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.CoefficientDescentSemantics

/-!
# Coordinate descent execution regressions

The tests retain leading zeros, reject an interior non-base coefficient and distinguish output
preparation from final emission. They use kernel reduction, not a trusted native computation.
-/

@[expose] public section

namespace QuadraticAlgebra.CoefficientDescentMachine

/-- All base coordinates descend without changing their order or physical width. -/
example : runFuel 10 (.start [⟨0, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩] : Configuration ℕ 2 0) =
    (.done (some [0, 2, 3]),
      { equalities := 3, control := 10, data := 43, constants := 1, output := 1 }) := by decide

/-- The last instruction emits the prepared result and is included in the cost. -/
example : runFuel 9 (.start [⟨0, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩] : Configuration ℕ 2 0) =
    (.emit (some [0, 2, 3]),
      { equalities := 3, control := 9, data := 41, constants := 1 }) := by decide

/-- A nonzero imaginary coordinate rejects, rather than silently projecting to its real part. -/
example : runFuel 4 (.start [⟨2, 0⟩, ⟨3, 1⟩, ⟨4, 0⟩] : Configuration ℕ 2 0) =
    (.done none,
      { equalities := 2, control := 4, data := 14, constants := 1, output := 1 }) := by decide

/-- An empty vector still pays initialization and output work. -/
example : runFuel 4 (.start [] : Configuration ℕ 2 0) =
    (.done (some []), { control := 4, data := 10, constants := 1, output := 1 }) := by decide

end QuadraticAlgebra.CoefficientDescentMachine
