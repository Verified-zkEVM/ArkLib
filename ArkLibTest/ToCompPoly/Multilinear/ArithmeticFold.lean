/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Multilinear.ArithmeticFold
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-! # Exact adjacent-pair folding, formal substitution, and primitive request order -/

open CompPoly CMlPolynomialEval OracleComp OracleSpec
namespace ArithmeticFoldTests

-- The generic instruction interface accepts an arbitrary unused inverse operation.
local instance : Inv ℤ := ⟨fun _ => 0⟩

/-- This generic caller executes the measured fold directly. -/
def caller {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : Nat}
    (table : CMlPolynomialEval F (n + 1)) (r : F) : CMlPolynomialEval F n :=
  simulateQ arithmeticAnswer (evalMleLayerProgram table r)

theorem caller_eq {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : Nat}
    (table : CMlPolynomialEval F (n + 1)) (r : F) :
    caller table r = evalMleLayer table r := simulateQ_evalMleLayerProgram table r

-- Formal transport uses the existing MLE head-fold theorem, with no finite-field point shortcut.
theorem caller_MLE {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : Nat}
    (table : CMlPolynomialEval F (n + 1)) (r : F) :
    MvPolynomial.MLE (fun u => (caller table r).get (finFunctionFinEquiv u)) =
      Polynomial.eval (MvPolynomial.C r) (MvPolynomial.finSuccEquiv F n
        (MvPolynomial.MLE (fun u => table.get (finFunctionFinEquiv u)))) := by
  rw [caller_eq]
  exact MLE_evalMleLayer table r

def table : CMlPolynomialEval ℤ 3 := #v[2, 3, 5, 11, 13, 17, 19, 23]

#eval (show IO _ from do
  let (p, cost) := profileArithmetic (evalMleLayerProgram (n := 2) table 7)
  unless p == #v[9, 47, 41, 47] && caller (n := 1) p (-2) == #v[-67, 29] &&
      caller (n := 2) table 0 == #v[2, 5, 13, 19] &&
      caller (n := 2) table 1 == #v[3, 11, 17, 23] &&
      cost .sub == 4 && cost .mul == 4 && cost .add == 4 && cost .valueRead == 8 &&
      cost .inv == 0 && cost .eq == 0 && cost .coefficientRead == 0 &&
      cost .nodeRead == 0 && cost .metadata == 0 do
    throw (IO.userError "incorrect adjacent fold, endian order or one-product profile")
  pure p)

def record (expected : Array ℤ) :
    QueryImpl (ArithmeticSpec ℤ) (StateM (List (Nat × Nat × Bool))) := fun op => do
  let tag := match op with
    | .valueRead p i => (0, i, p == expected)
    | .sub _ _ => (1, 0, true)
    | .mul _ _ => (2, 0, true)
    | .add _ _ => (3, 0, true)
    | _ => (4, 0, false)
  modify (· ++ [tag])
  pure (arithmeticAnswer op)

#eval (show IO _ from do
  let (p, trace) := (simulateQ (record table.toArray)
    (evalMleLayerProgram (n := 2) table 7)).run []
  let rowTrace (j : Nat) :=
    [(0, 2 * j, true), (0, 2 * j + 1, true), (1, 0, true), (2, 0, true), (3, 0, true)]
  unless p == #v[9, 47, 41, 47] && trace ==
      (List.range 4).flatMap rowTrace do
    throw (IO.userError "fold failed per-row difference/product or original adjacent-read trace")
  pure trace.length)

#eval (show IO _ from do
  let zeroDivisor : CMlPolynomialEval (ZMod 4) 2 := #v[0, 2, 1, 3]
  let (p, cost) := profileArithmetic (evalMleLayerProgram (n := 1) zeroDivisor 2)
  let trivial := caller (n := 0) (#v[0, 0] : CMlPolynomialEval (ZMod 1) 1) 0
  unless p == #v[0, 1] && cost .sub == 2 && cost .mul == 2 && cost .inv == 0 && trivial == #v[0] &&
      caller (n := 0) (#v[(2 : ℤ), 3]) 5 == #v[7] do
    throw (IO.userError "fold introduced a field, nonzero-factor or nontrivial-ring assumption")
  pure (p, trivial))

-- An ordinary compiled large table traversal, without a large kernel decide proof.
#eval (show IO _ from do
  let input : CMlPolynomialEval ℚ 17 := Vector.replicate (2 ^ 17) 3
  let output := caller (n := 16) input 7
  unless output.toArray.all (· == 3) && output.toArray.size == 65536 do
    throw (IO.userError "large measured head fold returned incorrect entries")
  pure output.toArray.size)

open Lean Elab Command in
run_cmd do
  for name in #[``evalMleLayerProgram, ``evalMleLayerCost, ``caller, ``record] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_evalMleLayerProgram, ``simulateQ_evalMleLayerProgram,
      ``caller_eq, ``caller_MLE] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end ArithmeticFoldTests
