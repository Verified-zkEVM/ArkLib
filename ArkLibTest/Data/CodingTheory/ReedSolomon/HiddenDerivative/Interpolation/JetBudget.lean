/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Support.Machine
/-!
# Executed support with an independent jet budget

At ambient degree one and multiplicity one, the differential weight of `Y₁` is zero.
Changing only the strict jet budget must therefore add `Y₁` and `Y₁²`. These runs reject a
hardcoded `2*m` cutoff and either direction of an off-by-one error in the new budget.
-/

namespace ArkLibTest.ReedSolomon.HiddenDerivative.Interpolation

open ReedSolomon.HiddenDerivative.InterpolationSupportMachine

private def columns (J : ℕ) : List (List ℕ) :=
  match (enumerateWithBudget 1 1 1 J 1).1 with
  | .done xs => xs
  | _ => []

example : columns 1 = [[0, 0, 0]] ∧
    columns 3 = [[0, 0, 0], [0, 0, 1], [0, 0, 2]] := by decide

end ArkLibTest.ReedSolomon.HiddenDerivative.Interpolation
