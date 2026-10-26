/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomialCost
import Lean.Compiler.IR

/-! # Certified affine and padded subtraction profiles -/

namespace CompPoly.Arithmetic.PaddedTest

open OracleComp OracleSpec

/-- An external caller executes the certified affine program. -/
def affineCaller {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (a b : F) : CPolynomial.Raw F :=
  (simulateQ arithmeticAnswer (affineRaw a b)).val

/-- An external caller executes padded subtraction without canonicalization. -/
def subCaller {F : Type} [AddGroup F] [Mul F] [Inv F] [DecidableEq F]
    (p q : CPolynomial.Raw F) : CPolynomial.Raw F :=
  (simulateQ arithmeticAnswer (subRaw p q)).val

example {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F] (a b : F) :
    affineCaller a b = CPolynomial.Raw.affine a b :=
  (simulateQ arithmeticAnswer (affineRaw a b)).property

example {F : Type} [AddGroup F] [Mul F] [Inv F] [DecidableEq F]
    (p q : CPolynomial.Raw F) : subCaller p q = CPolynomial.Raw.subRaw p q :=
  (simulateQ arithmeticAnswer (subRaw p q)).property

example {F : Type} [AddGroup F] [Mul F] [Inv F] [DecidableEq F]
    (p q : CPolynomial.Raw F) : (profileArithmetic (subRaw p q)).2 .eq = 0 := by
  rw [profileArithmetic_subRaw]
  rfl

#eval (show IO _ from do
  let (a, c) := profileArithmetic (affineRaw (3 : ℚ) 3)
  unless a.val == #[3, 0] && c .sub == 1 && c .eq == 0 && c .inv == 0 do
    throw (IO.userError "incorrect affine arithmetic profile")
  pure (a.val, c .sub, c .eq, c .inv))

#eval (show IO _ from do
  let (d, c) := profileArithmetic (subRaw (#[2, 4, 0] : CPolynomial.Raw ℚ) #[2, 4, 0])
  unless d.val == #[0, 0, 0] && c .add == 3 && c .sub == 3 &&
      c .coefficientRead == 9 && c .metadata == 8 && c .eq == 0 && c .inv == 0 do
    throw (IO.userError "incorrect padded subtraction profile")
  pure (d.val, c .add, c .sub, c .coefficientRead, c .metadata))

#eval (show IO _ from do
  let (d, c) := profileArithmetic (subRaw (#[] : CPolynomial.Raw ℚ) #[])
  unless d.val.isEmpty && c .metadata == 2 && c .add == 0 && c .sub == 0 do
    throw (IO.userError "incorrect empty padded subtraction profile")
  pure (d.val, c .metadata))

open Lean Elab Command

run_cmd do
  for name in #[``affineRaw, ``subRaw, ``affineCaller, ``subCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_affineRaw, ``profileArithmetic_subRaw] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.Arithmetic.PaddedTest
