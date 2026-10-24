/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToCompPoly.Univariate.Raw.Basic
import Lean.Compiler.IR

/-! # Padded coefficient arithmetic acceptance checks -/

namespace CompPoly.CPolynomial.Raw.BasicTest

/-- A generic caller needs only subtraction to construct an affine coefficient row. -/
def affineCaller {R : Type*} [Sub R] (a b : R) : Raw R := affine a b

/-- A generic caller retains padding when subtracting arrays. -/
def subCaller {R : Type*} [Zero R] [Add R] [Neg R] (p q : Raw R) : Raw R := subRaw p q

example : affineCaller (2 : ℤ) 5 = #[2, 3] := by decide
example : affineCaller (3 : ℤ) 3 = #[3, 0] := by decide
example : affineCaller (0 : ℤ) 0 = #[0, 0] := by decide
example : (subCaller (#[2, 4, 0] : Raw ℤ) #[2, 4]).size = 3 := by
  rw [subCaller, size_subRaw]
  decide

example {R : Type*} [Ring R] (p : Raw R) : (subCaller p p).toPoly = 0 := by
  rw [subCaller, toPoly_subRaw, sub_self]

example {R : Type*} [Ring R] (a b : R) :
    (affineCaller a b).toPoly.coeff 1 = b - a := by
  rw [affineCaller, toPoly_affine]
  simp

#eval (show IO _ from do
  let a := affineCaller (3 : ℤ) 3
  let d := subCaller (#[2, 4, 0] : Raw ℤ) #[2, 4]
  let left := subCaller (#[] : Raw ℤ) #[1, 2]
  let right := subCaller (#[1, 2] : Raw ℤ) #[]
  -- Empty right convolution still leaves its padded shifted row.
  let p := mulRaw (#[2, 3] : Raw ℤ) #[]
  unless a == #[3, 0] && d == #[0, 0, 0] && left == #[-1, -2] &&
      right == #[1, 2] && p == #[0] do
    throw (IO.userError "padded coefficient arithmetic changed its stored representation")
  pure (a, d, p))

open Lean Elab Command

run_cmd do
  for name in #[``affine, ``subRaw, ``affineCaller, ``subCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``size_affine, ``toPoly_affine, ``toPoly_mulRaw, ``toPoly_smul,
      ``size_subRaw, ``toPoly_subRaw] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.CPolynomial.Raw.BasicTest
