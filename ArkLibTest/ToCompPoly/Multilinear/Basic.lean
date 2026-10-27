/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Multilinear.Basic
import Lean.Compiler.IR

/-! # Shared Boolean Lagrange table acceptance checks -/

namespace CompPoly.CMlPolynomialEval.FastBasisTest

/-- An external caller explicitly selecting the shared recursive construction. -/
def fastCaller {R : Type*} [CommRing R] {n : ℕ} (w : Vector R n) : Vector R (2 ^ n) :=
  lagrangeBasisFast w

/-- A caller compiled after importing the extension obtains its compiler replacement. -/
def canonicalCaller {R : Type*} [CommRing R] {n : ℕ} (w : Vector R n) : Vector R (2 ^ n) :=
  lagrangeBasis w

example : fastCaller (#v[] : Vector ℤ 0) = #v[1] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(0 : ℤ)] = #v[1, 0] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(1 : ℤ)] = #v[0, 1] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(2 : ℤ)] = #v[-1, 2] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(0 : ℤ), 1] = #v[0, 0, 1, 0] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(1 : ℤ), 0] = #v[0, 1, 0, 0] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(2 : ℤ), 3] = #v[2, -4, -3, 6] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide
example : fastCaller #v[(2 : ℤ), 3, 5] = #v[-8, 16, 12, -24, 10, -20, -15, 30] := by
  rw [fastCaller, lagrangeBasisFast_eq]
  decide

/-- The algorithm agrees with the product specification in every commutative ring. -/
example {R : Type*} [CommRing R] {n : ℕ} (w : Vector R n) :
    fastCaller w = lagrangeBasis w := lagrangeBasisFast_eq w

#eval (show IO _ from do
  let b := fastCaller #v[(2 : ℤ), 3]
  unless b == #v[2, -4, -3, 6] do throw (IO.userError "incorrect two-coordinate table")
  pure b)
#eval (show IO _ from do
  let b := canonicalCaller #v[(2 : ℤ), 3, 5]
  unless b == #v[-8, 16, 12, -24, 10, -20, -15, 30] do
    throw (IO.userError "incorrect three-coordinate table")
  pure b)

-- Large runtime-only calls exercise the array-building loop rather than kernel reduction.
#eval (show IO _ from do
  let b := fastCaller (Vector.replicate 18 (0 : ℤ))
  let summary := (b.size, b[0]!, b.toArray.foldl (· + ·) 0)
  unless summary == (262144, 1, 1) do throw (IO.userError "incorrect large recursive table")
  pure summary)
#eval (show IO _ from do
  let b := canonicalCaller (Vector.replicate 18 (0 : ℤ))
  let summary := (b.size, b[0]!, b.toArray.foldl (· + ·) 0)
  unless summary == (262144, 1, 1) do throw (IO.userError "incorrect large canonical table")
  pure summary)

open Lean Elab Command

run_cmd do
  for name in #[``lagrangeBasisWith, ``lagrangeBasisFast, ``fastCaller, ``canonicalCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"

run_cmd do
  let some decl := Lean.IR.findEnvDecl (← getEnv) ``canonicalCaller
    | throwError "missing canonical caller IR"
  unless ((Lean.IR.formatDecl decl).pretty.splitOn "lagrangeBasisFast").length > 1 do
    throwError "canonical caller did not compile to the shared table builder"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``lagrangeBasisFast_zero, ``lagrangeBasisFast_succ,
      ``lagrangeBasis_get_even, ``lagrangeBasis_get_odd, ``lagrangeBasisFast_eq,
      ``lagrangeBasis_eq_lagrangeBasisFast] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.CMlPolynomialEval.FastBasisTest
