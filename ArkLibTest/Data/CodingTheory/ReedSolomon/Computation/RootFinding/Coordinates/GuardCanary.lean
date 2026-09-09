/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.GuardRefinement
/-!
# Actual coordinate guard checks

Earlier failures short-circuit. Actual selected-center equality tests both coordinates, and
residual payloads materialize zero translation even when the candidate's center is nonzero.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticCanonicalGuardMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[], [(1, 1)], 0, (1, 1), [((1, 0), [])]⟩
private def payload : QuadraticResidualBatch.Input (ZMod 5) := ⟨[], [], (0, 0), 0⟩
private def output : Configuration (ZMod 5) → Option Bool
  | .done b => some b
  | _ => none
private def center : Configuration (ZMod 5) → Option (Pair (ZMod 5))
  | .zero payload _ _ => some payload.center
  | _ => none

/-- The actual earlier-equation Boolean and both coordinates of the selected center matter. -/
example :
    output (runFuel 2 input 2 (.zero payload [] (.done false))).1 = some false ∧
    output (runFuel 2 input 11 (.witness payload (.done (some (1, 1))))).1 = some true ∧
    output (runFuel 2 input 11 (.witness payload (.done (some (1, 2))))).1 = some false ∧
    output (runFuel 2 input 11 (.witness payload (.done (some (2, 1))))).1 = some false ∧
    output (runFuel 2 input 2 (.witness payload (.done none))).1 = some false := by
  decide +kernel

/-- Residual launches allocate their real zero pair and retained fields with charged accesses. -/
example :
    center (runFuel 2 input 1 (.scan [[]])).1 = some (0, 0) ∧
    (runFuel 2 input 1 (.scan [[]])).2.base.data = 11 ∧
    (runFuel 2 input 1 (.scan [[]])).2.base.constants = 2 ∧
    (runFuel 2 input 1 (.zero payload [] (.start [(1, 1)]))).2.base.data = 9 ∧
    (runFuel 2 input 1 (.witness payload (.done (some (1, 1))))).2.base.data = 11 := by
  decide +kernel

/-- A whole guard accepts only after its zero equation, nonzero witness and center test execute. -/
example :
    output (runFuel 2 input 256 (.start [[]])).1 = some true ∧
    output (runFuel 2 { input with separant := [] } 128 (.start [])).1 = some false := by
  decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticCanonicalGuardMachine
