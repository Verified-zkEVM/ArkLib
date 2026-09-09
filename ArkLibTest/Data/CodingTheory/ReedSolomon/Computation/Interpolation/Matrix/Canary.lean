/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Matrix.Semantics
/-!
# Kernel canaries for full received matrices

Literal outputs test column width on empty input, ordered distinct and repeated point blocks,
zero multiplicity/support, explicit point/row counters, and complete observed charges.
-/

namespace ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine

example : countCells [10, 20, 30] = (3, 128) := by decide

example : countCells ([] : List ℕ) = (0, 32) := by decide

example : run 0 0 1 1 ([] : List (ℤ × ℤ)) = (some ⟨2, 0, 0, []⟩, 1029) := by decide

example : run 0 0 1 1 [((2 : ℤ), 3), (4, 5)] =
    (some ⟨2, 2, 4, [([1, 3], 0), ([1, 3], 0), ([1, 5], 0), ([1, 5], 0)]⟩, 10871) := by decide

example : run 0 0 1 1 [((2 : ℤ), 3), (2, 3)] =
    (some ⟨2, 2, 4, [([1, 3], 0), ([1, 3], 0), ([1, 3], 0), ([1, 3], 0)]⟩, 10871) := by decide

example : run 0 0 0 1 [((2 : ℤ), 3), (4, 5)] = (some ⟨0, 2, 0, []⟩, 1667) := by decide

example : run 0 0 1 0 [((2 : ℤ), 3)] = (some ⟨0, 1, 0, []⟩, 1366) := by decide

example : traverse 0 0 1 1 7 ([] : List (ℤ × ℤ)) = (some ⟨7, 0, 0, []⟩, 32) := by decide

end ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine
