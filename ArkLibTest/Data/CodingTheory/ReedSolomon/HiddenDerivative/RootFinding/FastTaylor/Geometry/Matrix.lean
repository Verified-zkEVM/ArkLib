/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Matrix
import Mathlib.Algebra.Field.ZMod

/-! Nontrivial pivot division, coordinate ordering, zero direction, and one-dimensional matrices. -/

namespace ProjectionMatrixTests

open ReedSolomon.HiddenDerivative.FastTaylor.Geometry.ProjectionMatrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def direction : Fin 3 → ℚ := ![0, 2, 3]

example : forward direction 1 * backward direction 1 = 1 :=
  forward_mul_backward direction 1 (by decide)

/-- Execute matrix construction and explicit inverse action for several pivot positions. -/
def run : IO Unit := do
  unless selectPivot direction == some 1 do
    throw (IO.userError "projection pivot search did not skip leading zero")
  let some (m, n) := construct? direction | throw (IO.userError "nonzero direction rejected")
  unless decide (m = !![1, 0, 0; 0, 0, 2; 0, 1, 3]) do
    throw (IO.userError "projection columns have the wrong coordinate order")
  unless decide (n = !![1, 0, 0; 0, -(3 / 2 : ℚ), 1; 0, (1 / 2 : ℚ), 0]) do
    throw (IO.userError "explicit inverse did not divide by the pivot")
  unless decide (m * n = 1 ∧ n * m = 1) do
    throw (IO.userError "constructed matrices are not two-sided inverses")
  unless decide (n.mulVec ![5, 8, 7] = ![5, -5, 4]) do
    throw (IO.userError "inverse coordinate formula failed")
  unless (construct? (0 : Fin 3 → ℚ)).isNone do
    throw (IO.userError "zero direction incorrectly accepted")
  let some (m₀, n₀) := construct? (![3] : Fin 1 → ℚ) |
    throw (IO.userError "one-dimensional direction rejected")
  unless m₀ 0 0 == 3 && n₀ 0 0 == (1 / 3 : ℚ) do
    throw (IO.userError "one-dimensional projection failed")
  let w : Fin 3 → ZMod 5 := ![0, 0, 2]
  let some (mf, nf) := construct? w | throw (IO.userError "last-coordinate pivot rejected")
  unless decide (mf * nf = 1 ∧ nf * mf = 1) && nf 2 2 == 3 do
    throw (IO.userError "positive-characteristic pivot inversion failed")

end ProjectionMatrixTests
