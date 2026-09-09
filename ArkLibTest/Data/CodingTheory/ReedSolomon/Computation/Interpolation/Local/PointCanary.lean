/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.PointSpec
/-!
# Kernel canaries for materialized interpolation point blocks

Literal rows and charges distinguish duplicate-aware lookup, cancellation, explicit homogeneous
augmentation, empty support, and actual support enumeration followed by column execution.
-/

namespace ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine

example : block [[((1 : ℤ), [0, 0]), (2, [0, 0])], [(4, [1, 0])]] =
    ([([3, 0], 0), ([3, 0], 0), ([0, 4], 0)], 1952) := by decide

example : block [[((1 : ℤ), [0, 0]), (-1, [0, 0])], [(2, [0, 0])]] =
    ([([0, 2], 0), ([0, 2], 0), ([0, 2], 0)], 2208) := by decide

example : (assemble 0 0 1 1 (2 : ℤ) 3).1 = some [([1, 3], 0), ([1, 3], 0)] := by decide

example : assemble 0 0 1 1 (2 : ℤ) 3 = (some [([1, 3], 0), ([1, 3], 0)], 4697) := by decide

example : assemble 2 1 1 1 (2 : ℤ) 3 = (some [([1], 0)], 3173) := by decide

example : assemble 0 0 0 1 (2 : ℤ) 3 = (some [], 513) := by decide

example : assemble 0 0 1 0 (2 : ℤ) 3 = (some [], 667) := by decide

example : columns 1 2 (2 : ℤ) 3 [[]] = (none, 64) := by decide

example : dot ([1, 3] : List ℤ) (fun i => if i = 0 then 3 else -1) = 0 := by
  norm_num [dot, Finset.sum_range_succ]

example : block ([[]] : List (DenseColumn ℤ)) = ([], 192) := by decide

end ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine
