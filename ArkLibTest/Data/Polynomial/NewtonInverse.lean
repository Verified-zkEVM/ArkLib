/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.NewtonInverse
import ArkLib.Data.MvPolynomial.BoxAlgebra
import Mathlib.Data.ZMod.Basic

/-! Newton updates over mixed parameter nilpotents, including characteristic two. -/

namespace NewtonInverseTests

open CPoly CPoly.BoxAlgebra Polynomial.NewtonInverse

private abbrev A := Carrier 2 2 ℤ
private def error : A := eps 0 + eps 1
private def value : A := 1 - error

example (a b : A) (h : (1 - a * b) ^ 3 = 0) : a * correct 3 a b = 1 :=
  right_inverse 3 a b h

example : rounds 3 = 2 := by decide
example : rounds 8 = 3 := by decide
example : rounds 9 = 4 := by decide

/-- Execute the update count, residual squaring, and complete nilpotent correction. -/
def run : IO Unit := do
  unless error ^ 2 != 0 && error ^ 3 == 0 do
    throw (IO.userError "mixed residual does not distinguish coordinate and ideal precision")
  let first := step value 1
  unless 1 - value * first == error ^ 2 && value * first != 1 do
    throw (IO.userError "first Newton update failed to square the mixed residual")
  let inverse := correct 3 value 1
  unless rounds 3 == 2 && rounds 8 == 3 && rounds 9 == 4 do
    throw (IO.userError "Newton correction did not choose the least doubling count")
  unless inverse == 1 + error + error ^ 2 do
    throw (IO.userError "Newton inverse differs from the finite nilpotent inverse")
  unless value * inverse == 1 && inverse * value == 1 do
    throw (IO.userError "Newton correction did not return a two-sided inverse")
  unless correct 0 value 1 == 1 && correct 1 value 1 == 1 do
    throw (IO.userError "zero-round precision changed the supplied approximation")
  -- No division by two is available: the update must still work in characteristic two.
  let t : Carrier 1 3 (ZMod 2) := eps 0
  let a := 1 - t
  unless 1 - a * step a 1 == t ^ 2 && t ^ 2 != 0 do
    throw (IO.userError "characteristic-two Newton residual failed")
  unless a * correct 3 a 1 == 1 do
    throw (IO.userError "Newton inverse incorrectly requires two to be invertible")

end NewtonInverseTests
