/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.NilpotentInverse
import ArkLib.Data.MvPolynomial.BoxAlgebra
import Mathlib.Tactic.Ring

/-! Finite inverse correction over a genuinely nonreduced two-parameter coefficient ring. -/

open CPoly Polynomial.NilpotentInverse

namespace NilpotentInverseTests

private instance : Fact (0 < 2) := ⟨by decide⟩
private abbrev A := BoxAlgebra.Carrier 2 2 ℤ
private def e₀ : A := BoxAlgebra.eps 0
private def e₁ : A := BoxAlgebra.eps 1

private theorem mixed_cube : (e₀ + e₁) ^ 3 = 0 := by
  have h₀ : e₀ ^ 2 = 0 := BoxAlgebra.eps_pow 0
  have h₁ : e₁ ^ 2 = 0 := BoxAlgebra.eps_pow 1
  calc
    (e₀ + e₁) ^ 3 = e₀ ^ 2 * (e₀ + 3 * e₁) + e₁ ^ 2 * (3 * e₀ + e₁) := by ring
    _ = 0 := by rw [h₀, h₁]; simp

private def a : A := 1 - (e₀ + e₁)

private theorem residual_cube : (1 - a * 1) ^ 3 = 0 := by
  simpa [a] using mixed_cube

example : a * correct 3 a 1 = 1 := right_inverse 3 a 1 residual_cube
example : correct 3 a 1 * a = 1 := left_inverse 3 a 1 residual_cube
example : correct 0 a 1 = 0 := correct_zero a 1

/-- A mixed residual needs exponent three, although each individual parameter squares to zero. -/
def run : IO Unit := do
  let e := e₀ + e₁
  unless (e ^ 2).val.coeff #m[1, 1] = 2 do
    throw (IO.userError "mixed residual square unexpectedly vanished")
  unless e ^ 3 == 0 do
    throw (IO.userError "mixed residual cube did not vanish")
  let c := correct 3 a 1
  unless c.val.coeff #m[1, 1] = 2 do
    throw (IO.userError "inverse correction omitted mixed coefficient")
  unless c == 1 + e₀ + e₁ + 2 * (e₀ * e₁) do
    throw (IO.userError "finite inverse correction has wrong coefficients")
  unless a * c == 1 do
    throw (IO.userError "finite correction is not a right inverse")
  unless c * a == 1 do
    throw (IO.userError "finite correction is not a left inverse")
  unless a * correct 2 a 1 != 1 do
    throw (IO.userError "insufficient residual precision incorrectly inverted")
  unless correct 0 a 1 == 0 do
    throw (IO.userError "precision zero correction is not zero")
  unless (unit 3 a 1 residual_cube).inv == c do
    throw (IO.userError "unit wrapper changed computed inverse")

end NilpotentInverseTests
