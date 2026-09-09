/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.WitnessRefinement
/-!
# Kernel checks of the actual coordinate witness search

Both coordinates participate in each scalar equality. Zero entries advance in order; the first
nonzero entry supplies the emitted point. Retained payload slots and zero literals are charged.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticResidualWitnessMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[], [], (1, 1), 0⟩
private def output : Configuration (ZMod 5) → Option (Option (Pair (ZMod 5)))
  | .done out => some out
  | _ => none

/-- Both imaginary-only and real-only residuals produce the actual first nonzero witness. -/
example :
    output (runFuel 2 input 12 (.scan [((1, 1), (0, 0))])).1 = some none ∧
    output (runFuel 2 input 11 (.scan [((1, 1), (0, 2))])).1 = some (some (1, 1)) ∧
    output (runFuel 2 input 11 (.scan [((2, 3), (2, 0))])).1 = some (some (2, 3)) ∧
    output (runFuel 2 input 21
      (.scan [((1, 1), (0, 0)), ((2, 3), (0, 1)), ((4, 4), (1, 1))])).1 =
      some (some (2, 3)) := by
  decide +kernel

/-- Point retention, the residual payload, zero literals and actual delegated instructions cost. -/
example :
    (runFuel 2 input 1 (.start [])).2.base.data = 7 ∧
    (runFuel 2 input 1 (.scan [((1, 1), (0, 0))])).2.base.constants = 2 ∧
    (runFuel 2 input 1 (.scan [((1, 1), (0, 0))])).2.base.data = 11 ∧
    (runFuel 2 input 1 (.check (1, 1) [] ⟨2, (0, 0), (0, 0)⟩ (.start .equal))).2 =
      ⟨{ control := 2, data := 13, constants := 10 }, 0⟩ := by
  decide +kernel

/-- The full actual batch executes before scanning; a suspended emit is not a returned witness. -/
example :
    output (runFuel 2 input 43 (.start [(1, 1)])).1 = some none ∧
    output (runFuel 2 input 0 (.emit (some (2, 3)))).1 = none ∧
    (runFuel 2 input 1 (.emit (some (2, 3)))).2.base.output = 1 := by
  decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticResidualWitnessMachine
