/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Frobenius

/-! Repeated contraction preserves multiplicities divisible by the square of the characteristic. -/

namespace FullSquarefreeFrobeniusTests

open CompPoly CompPoly.CPolynomial
open CompPoly.CPolynomial.FullSquarefreeDecomposition

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A multiplicity-nine factor survives two contractions in characteristic three. -/
def run : IO Unit := do
  let x : CPolynomial (ZMod 3) := X
  let base := (x - 1) * (x + 1) ^ 2
  let f := base ^ 9
  unless f.derivative == 0 do
    throw (IO.userError "ninth power has nonzero derivative in characteristic three")
  let once := primeContract 3 f
  unless once == base ^ 3 && once ^ 3 == f do
    throw (IO.userError "first contraction lost a multiplicity-nine factor")
  unless once.derivative == 0 do
    throw (IO.userError "first contraction should still have zero derivative")
  let twice := primeContract 3 once
  unless twice == base && twice ^ 9 == f do
    throw (IO.userError "second contraction did not restore multiplicities one and two")
  unless twice.natDegree < once.natDegree && once.natDegree < f.natDegree do
    throw (IO.userError "repeated contraction did not strictly decrease degree")
  unless primeContract 3 (0 : CPolynomial (ZMod 3)) == 0 do
    throw (IO.userError "zero contraction changed the polynomial")
  unless primeContract 3 (C (2 : ZMod 3)) == C (2 : ZMod 3) do
    throw (IO.userError "prime-field coefficient contraction is not the identity")

end FullSquarefreeFrobeniusTests
