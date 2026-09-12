/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.StoredFraction

/-! Executed rational-function arithmetic with nonconstant denominators and gcd cancellation. -/

open CompPoly CPolynomial Polynomial.FunctionFieldAlgorithms

namespace FunctionFieldAlgorithmsTests

private abbrev P := CPolynomial ℚ
private def x : P := CPolynomial.X
private def a : Fraction ℚ := ⟨(x + 1) * (x + 2), (x + 1) * (x + 3)⟩

example (p q r : P) : exactDivide p q = some r ↔ q ≠ 0 ∧ r * q = p :=
  exactDivide_eq_some_iff p q r

example (b : Fraction ℚ) (hb : b.Valid) : b.cancelGcd.value = b.value :=
  Fraction.value_cancelGcd hb

/-- Distinguish nontrivial gcd cancellation, rational arithmetic and rejected division. -/
def run : IO Unit := do
  let reduced := a.cancelGcd
  unless reduced.num == x + 2 do
    throw (IO.userError "gcd cancellation returned wrong numerator")
  unless reduced.den == x + 3 do
    throw (IO.userError "gcd cancellation lost the nonconstant denominator")
  unless (gcdMonic a.num a.den).natDegree == 1 do
    throw (IO.userError "test failed to exercise a nontrivial gcd")
  let b : Fraction ℚ := ⟨1, x + 3⟩
  let c := reduced.add b
  unless c.num == (x + 3) * (x + 3) do
    throw (IO.userError "rational addition returned wrong numerator")
  unless c.den == (x + 3) * (x + 3) do
    throw (IO.userError "rational addition returned wrong denominator")
  let product := reduced.mul reduced.inv
  unless product.num == product.den do
    throw (IO.userError "nonzero rational inverse failed")
  let zeroInverse := (Fraction.ofPolynomial (0 : P)).inv
  unless zeroInverse.num == 0 && zeroInverse.den == 1 do
    throw (IO.userError "zero inverse did not use field convention")
  unless exactDivide ((x + 1) * (x + 2)) (x + 1) == some (x + 2) do
    throw (IO.userError "exact division rejected a nontrivial factor")
  unless exactDivide (x + 2) (x + 1) == none do
    throw (IO.userError "inexact division was accepted")
  unless exactDivide (0 : P) 0 == none do
    throw (IO.userError "zero divisor was accepted")
  unless exactDivide (x + 1) (CPolynomial.C 2) == some ((1 / 2 : ℚ) • (x + 1)) do
    throw (IO.userError "unit normalization by exact division failed")

end FunctionFieldAlgorithmsTests
