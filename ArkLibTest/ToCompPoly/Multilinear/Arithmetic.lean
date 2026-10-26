/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Multilinear.Arithmetic
import Lean.Compiler.IR

/-! # Shared Lagrange-table arithmetic profiles -/

namespace CompPoly.CMlPolynomialEval.FastBasisArithmeticTest

open OracleComp OracleSpec

/-- An external caller executes the measured interpretation's certified arithmetic. -/
def arithmeticCaller {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : ℕ}
    (w : Vector F n) : CMlPolynomialEval F n :=
  simulateQ arithmeticAnswer (lagrangeBasisProgram w)

/-- An external caller retains the exact operation profile of the same program. -/
def profileCaller {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : ℕ}
    (w : Vector F n) : CMlPolynomialEval F n × ArithmeticCost :=
  profileArithmetic (lagrangeBasisProgram w)

example {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : ℕ} (w : Vector F n) :
    arithmeticCaller w = lagrangeBasis w := by
  rw [arithmeticCaller, simulateQ_lagrangeBasisProgram, lagrangeBasisFast_eq]

example {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : ℕ} (w : Vector F n) :
    (profileCaller w).2 .mul = 2 ^ (n + 1) - 2 := by
  rw [profileCaller, profileArithmetic_lagrangeBasisProgram]
  rfl

example {F : Type} [CommRing F] [Inv F] [DecidableEq F] {n : ℕ} (w : Vector F n) :
    (profileCaller w).2 .sub = n := by
  rw [profileCaller, profileArithmetic_lagrangeBasisProgram]
  rfl

example : lagrangeBasisCost 0 .mul = 0 := rfl
example : lagrangeBasisCost 0 .sub = 0 := rfl
example : lagrangeBasisCost 1 .mul = 2 := rfl
example : lagrangeBasisCost 3 .mul = 14 := rfl
example : lagrangeBasisCost 3 .sub = 3 := rfl
example (n : ℕ) : lagrangeBasisCost n .inv = 0 := rfl
example (n : ℕ) : lagrangeBasisCost n .eq = 0 := rfl

#eval (show IO _ from do
  let (b, c) := profileCaller (#v[] : Vector ℚ 0)
  unless b == #v[1] && c .mul == 0 && c .sub == 0 do
    throw (IO.userError "incorrect empty basis profile")
  pure (b, c .mul, c .sub))

#eval (show IO _ from do
  let (b, c) := profileCaller #v[(2 : ℚ), 3, 5]
  unless b == #v[-8, 16, 12, -24, 10, -20, -15, 30] &&
      c .mul == 14 && c .sub == 3 && c .inv == 0 && c .eq == 0 do
    throw (IO.userError "incorrect asymmetric basis profile")
  pure (b, c .mul, c .sub, c .inv, c .eq))

-- The interpreter must also execute a substantial monadic array traversal without kernel decide.
#eval (show IO _ from do
  let (b, c) := profileCaller (Vector.replicate 12 (0 : ℚ))
  unless b[0]! == 1 && b.toArray.foldl (· + ·) 0 == 1 &&
      c .mul == 8190 && c .sub == 12 && c .inv == 0 do
    throw (IO.userError "incorrect large basis profile")
  pure (b.size, c .mul, c .sub))

open Lean Elab Command

run_cmd do
  for name in #[``lagrangeBasisProgram, ``arithmeticCaller, ``profileCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_ofFnM_uniform, ``lagrangeBasisCost_succ,
      ``lagrangeBasisCost_mul_succ, ``lagrangeBasisCost_sub_succ,
      ``profileArithmetic_lagrangeBasisProgram, ``simulateQ_lagrangeBasisProgram] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.CMlPolynomialEval.FastBasisArithmeticTest
