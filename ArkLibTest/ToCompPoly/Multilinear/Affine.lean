/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToCompPoly.Multilinear.Affine
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-! # Adjacent affine row and formal restriction checks -/

namespace CompPoly.CMlPolynomialEval.AffineTest

open OracleComp OracleSpec MvPolynomial

/-- An external caller needs only the endpoint subtraction to construct a raw affine row. -/
def rowCaller {R : Type*} [Sub R] {n : ℕ}
    (table : CMlPolynomialEval R (n + 1)) (j : Fin (2 ^ n)) : CPolynomial.Raw R :=
  affineRow table j

/-- An external caller executes the certified endpoint-read program. -/
def arithmeticCaller {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F]
    [DecidableEq F] {n : ℕ} (table : CMlPolynomialEval F (n + 1)) (j : Fin (2 ^ n)) :
    CPolynomial.Raw F :=
  (simulateQ arithmeticAnswer (affineRowProgram table j)).val

/-- Distinct adjacent rows distinguish both little-endian suffix coordinates. -/
def asymmetricTable : CMlPolynomialEval ℤ 3 := #v[2, 5, 11, 17, 23, 31, 41, 47]

example : rowCaller asymmetricTable 0 = #[2, 3] := by decide
example : rowCaller asymmetricTable 1 = #[11, 6] := by decide
example : rowCaller asymmetricTable 2 = #[23, 8] := by decide
example : rowCaller asymmetricTable 3 = #[41, 6] := by decide

-- No suffix coordinates remain: the single row still leaves its head variable formal.
example : rowCaller (n := 0) (#v[(2 : ℤ), -5] : CMlPolynomialEval ℤ 1) 0 = #[2, -7] := by decide
example : rowCaller (n := 0) (#v[(3 : ℤ), 3] : CMlPolynomialEval ℤ 1) 0 = #[3, 0] := by decide

/-- Formal polynomial restriction holds in every characteristic, with no field-size premise. -/
example {R : Type*} [CommRing R] {n : ℕ}
    (table : CMlPolynomialEval R (n + 1)) (j : Fin (2 ^ n)) :
    (rowCaller table j).toPoly =
      Polynomial.map (MvPolynomial.eval (fun i => (finFunctionFinEquiv.symm j i : R)))
        (MvPolynomial.finSuccEquiv R n
          (MLE (fun x => table.get (finFunctionFinEquiv x)))) :=
  affineRow_toPoly table j

example : (rowCaller (n := 0) (#v[(1 : ZMod 2), 0] : CMlPolynomialEval (ZMod 2) 1) 0).toPoly =
    Polynomial.C 1 + Polynomial.X := by
  rw [rowCaller, affineRow, CPolynomial.Raw.toPoly_affine]
  simp [Vector.get_eq_getElem, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

example {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F] {n : ℕ}
    (table : CMlPolynomialEval F (n + 1)) (j : Fin (2 ^ n)) :
    arithmeticCaller table j = rowCaller table j :=
  (simulateQ arithmeticAnswer (affineRowProgram table j)).property

#eval (show IO _ from do
  let rows := (List.finRange 4).map (rowCaller asymmetricTable)
  unless rows == [#[2, 3], #[11, 6], #[23, 8], #[41, 6]] do
    throw (IO.userError "adjacent affine rows changed suffix ordering")
  pure rows)

#eval (show IO _ from do
  let table : CMlPolynomialEval ℚ 3 := #v[2, 5, 11, 17, 23, 31, 41, 47]
  let (p, c) := profileArithmetic (affineRowProgram table 2)
  unless p.val == #[23, 8] && c .valueRead == 2 && c .sub == 1 &&
      c .mul == 0 && c .eq == 0 && c .inv == 0 do
    throw (IO.userError "incorrect adjacent-row instruction profile")
  pure (p.val, c .valueRead, c .sub))

open Lean Elab Command

run_cmd do
  for name in #[``affineRow, ``affineRowProgram, ``rowCaller, ``arithmeticCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``size_affineRow, ``affineRow_toPoly, ``profileArithmetic_affineRowProgram] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.CMlPolynomialEval.AffineTest
