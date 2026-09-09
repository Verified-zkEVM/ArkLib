/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectArithmeticRefinement
/-!
# Kernel checks for the direct arithmetic suffix

Literal ledgers exercise all five base programs on the successful path, zero-slope rejection
before inverse, and a nonzero imaginary slope whose real coordinate is zero.
-/

namespace ReedSolomon.HiddenDerivative.DirectArithmeticMachine

private def observe : Configuration (ZMod 3) → Option (Option (Pair (ZMod 3)))
  | .ready (.done out) => some out
  | _ => none

private def success := runFuel (2 : ZMod 3) 61 (.ready (.negate (1, 1) (2, 0)))

example : (observe success.1, success.2) =
    (some (some (0, 2)), ⟨⟨5, 10, 4, 1, 2, 118, 440, 52, 6⟩, 0⟩) := by decide +kernel

private def rejected := runFuel (2 : ZMod 3) 29 (.ready (.negate (1, 1) (1, 1)))

example : (observe rejected.1, rejected.2) =
    (some none, ⟨⟨2, 0, 2, 0, 2, 56, 211, 32, 4⟩, 0⟩) := by decide +kernel

private def inversionOperands : Configuration (ZMod 3) → Option (Pair (ZMod 3) × Pair (ZMod 3))
  | .ready (.invert b s) => some (b, s)
  | _ => none

example : inversionOperands (runFuel (2 : ZMod 3) 10 (.ready (.test (1, 2) (0, 1)))).1 =
    some ((1, 2), (0, 1)) := by decide +kernel

end ReedSolomon.HiddenDerivative.DirectArithmeticMachine
