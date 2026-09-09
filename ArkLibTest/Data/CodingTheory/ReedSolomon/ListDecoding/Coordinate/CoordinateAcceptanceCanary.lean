/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateAcceptanceRefinement
/-! # Kernel checks of actual coordinate acceptance and short-circuiting -/

namespace ReedSolomon.ListDecoding.QuadraticCanonicalAcceptanceMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Guard.Input (ZMod 5) := ⟨[(2, 0)], [(1, 1)], 0, (1, 1), [((1, 0), [])]⟩
private def output : Configuration (ZMod 5) → Option (Option (List (ZMod 5)))
  | .done out => some out
  | _ => none

/-- Full acceptance runs the base filter; absent witnesses and imaginary cells fail. -/
example :
    output (runFuel 2 input 1 1 0 [] 512 (.start [[]])).1 = some (some [2]) ∧
    output (runFuel 2 { input with separant := [] } 1 1 0 [] 256 (.start [])).1 = some none ∧
    output (runFuel 2 { input with coefficients := [(2, 1)] }
      1 1 0 [] 512 (.start [])).1 = some none := by decide +kernel

/-- Immediate rejection pays only the return and emit instructions. -/
example :
    output (runFuel 2 input 1 1 0 [] 2 (.guard (.done false))).1 = some none ∧
    (runFuel 2 input 1 1 0 [] 2 (.guard (.done false))).2 = 6 := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticCanonicalAcceptanceMachine
