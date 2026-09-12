/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Residues
import Mathlib.Data.ZMod.Basic

/-! Executed residue-stage regressions in characteristic five. -/

namespace FullSquarefreeResidueTests

open CompPoly CompPoly.CPolynomial
open CompPoly.CPolynomial.FullSquarefreeDecomposition

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

/-- Mixed labels distinguish residue extraction from derivative radicalization.
The characteristic-divisible factor remains in the derivative gcd. -/
def run : IO Unit := do
  let x : CPolynomial F := X
  let f := x * (x - 1) ^ 2 * (x - 2) ^ 5 * (x - 3) ^ 7
  let some out := FullSquarefreeDecomposition.run 5 f
    | throw (IO.userError "mixed residue stage failed")
  unless out.strata.length == 2 do
    throw (IO.userError "residue loop did not stop after residue two")
  unless out.strata[0]!.1 == 1 && out.strata[0]!.2 == x do
    throw (IO.userError "residue one stratum is incorrect")
  unless out.strata[1]!.1 == 2 && out.strata[1]!.2 == (x - 1) * (x - 3) do
    throw (IO.userError "residue two omitted multiplicity seven")
  unless out.residual == 1 do
    throw (IO.userError "completed residue loop has nonunit residual")
  unless (derivativeParts f).1 * (out.strata.map Prod.snd).prod * out.residual == f do
    throw (IO.userError "residue stage lost factors")
  let some zeroDerivative := FullSquarefreeDecomposition.run 5 ((x - 2) ^ 5)
    | throw (IO.userError "derivative-zero residue stage failed")
  unless zeroDerivative.strata.isEmpty && zeroDerivative.residual == 1 do
    throw (IO.userError "derivative-zero input has spurious residues")
  unless (FullSquarefreeDecomposition.run 5 (0 : CPolynomial F)).isNone do
    throw (IO.userError "zero input was accepted")
  let some constant := FullSquarefreeDecomposition.run 5 (1 : CPolynomial F)
    | throw (IO.userError "unit input failed")
  unless constant.strata.isEmpty && constant.residual == 1 do
    throw (IO.userError "unit input has spurious strata")

end FullSquarefreeResidueTests
