/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.PreparationRefinement
/-! # Kernel checks for coordinate preparation and exact charges -/

namespace ReedSolomon.HiddenDerivative.QuadraticJetPreparationMachine

private abbrev P := Pair (ZMod 5)

example : runFuel 7 (.start 2 ([(1, 2), (3, 4)] : List P)) =
    (.done (some [(0, 0), (3, 4), (1, 2)]),
      ⟨{ control := 7, data := 35, constants := 2, output := 1 }, 8⟩) := by decide +kernel

example : runFuel 5 (.start 0 ([] : List P)) =
    (.done (some [(0, 0)]),
      ⟨{ control := 5, data := 19, constants := 2, output := 1 }, 4⟩) := by decide +kernel

example : runFuel 5 (.start 0 ([(1, 2), (3, 4)] : List P)) =
    (.done none, ⟨{ control := 4, data := 17, output := 1 }, 4⟩) := by decide +kernel

example : (runFuel 1 (.pad 1 ([] : List P))).2.base.constants = 2 := by decide +kernel
example : (runFuel 1 (.pad 1 ([] : List P))).2.base.data = 7 := by decide +kernel
example : (runFuel 1 (.pad 0 ([] : List P))).2.base.data = 3 := by decide +kernel
example : (runFuel 1 (.emit (none : Option (List P)))).2.base.output = 1 := by decide +kernel
example : (runFuel 2 (.start 2 ([(1, 2), (3, 4)] : List P))).1 =
    .scan 2 [(3, 4)] [(1, 2)] := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticJetPreparationMachine
