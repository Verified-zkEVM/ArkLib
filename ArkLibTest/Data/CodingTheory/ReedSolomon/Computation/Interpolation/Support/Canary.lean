/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Support.Machine
/-!
# Interpolation support execution boundaries

Concrete outputs distinguish strict versus non-strict cutoffs, X from jet degree, and the two
unequal derivative weights. Zero axes and zero derivative order exercise different boundaries.
-/

namespace ReedSolomon.HiddenDerivative.InterpolationSupportMachine

/-- Y₀ has weight two and Y₁ weight one; weight three and total jet degree two are excluded. -/
example : (enumerate 2 1 1 3).1 = .done
    [[0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 0], [1, 0, 1], [2, 0, 0]] := by decide

/-- Raising the ambient degree changes the actual output support. -/
example : (enumerate 3 1 1 3).1 = .done
    [[0, 0, 0], [0, 0, 1], [1, 0, 0], [2, 0, 0]] := by decide

/-- Derivative order zero still has the Y₀ coordinate; X is not part of the jet-degree sum. -/
example : (enumerate 1 0 1 3).1 = .done
    [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0]] := by decide

/-- Zero weights have the specified natural subtraction behavior outside the positive regime. -/
example : (enumerate 0 0 1 1).1 = .done [[0, 0], [0, 1]] := by decide

/-- Both ways of obtaining a zero X bound produce the empty support. -/
example : (enumerate 2 1 0 3).1 = .done [] ∧ (enumerate 2 1 1 0).1 = .done [] := by decide

/-- A generic box with no jet coordinates still enumerates X. -/
example : (runFuel ⟨2, 0, 1, 3⟩ (fuel ⟨2, 0, 1, 3⟩) .start).1 =
    .done [[0], [1], [2]] := by decide

/-- A strict zero jet cutoff rejects even the empty jet tuple. -/
example : (runFuel ⟨2, 0, 0, 3⟩ (fuel ⟨2, 0, 0, 3⟩) .start).1 = .done [] := by decide

/-- Insufficient fuel reports the actual unfinished range materialization. -/
example : runFuel ⟨2, 2, 2, 3⟩ 1 .start = (.rangeX 3 [], 32) := by decide

end ReedSolomon.HiddenDerivative.InterpolationSupportMachine
