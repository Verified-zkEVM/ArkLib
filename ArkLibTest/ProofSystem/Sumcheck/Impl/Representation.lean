/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Impl.Representation
import Mathlib.Algebra.Field.ZMod
import CompPoly.Univariate.ToPoly.Degree
import Lean.Compiler.IR

/-! # Canonical stored-length bound without field or Boolean-equality assumptions -/

open Sumcheck.Impl.Representation
namespace RepresentationSizeTests

example {R : Type} [CommSemiring R] (deg : Nat) (message : Message R deg) :
    message.val.val.size ≤ deg + 1 := size_le R deg message

def zeroMessage : Message Nat 0 := ⟨0, by decide⟩
def constantMessage : Message Nat 0 := ⟨CompPoly.CPolynomial.C 7,
  CompPoly.CPolynomial.degree_C_le 7⟩
def affineMessage : Message Nat 1 := ⟨CompPoly.CPolynomial.ofArray #[2,3,0], by
  apply (CompPoly.CPolynomial.degree_le_iff_coeff_zero _ _).mpr
  intro k hk
  rw [CompPoly.CPolynomial.coeff_ofArray]
  have hkNat : 1 < k := WithBot.coe_lt_coe.mp hk
  rcases k with _ | _ | k
  · omega
  · omega
  · cases k with
    | zero => decide
    | succ k =>
      have hsize : (#[2,3,0] : Array Nat).size ≤ k+1+1+1 := by
        change 3 ≤ k+1+1+1
        omega
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsize,
        Option.getD_none]⟩
def trivialMessage : Message (ZMod 1) 0 := ⟨0, by decide⟩

example : zeroMessage.val.val.size ≤ 1 := size_le Nat 0 zeroMessage
example : constantMessage.val.val.size ≤ 1 := size_le Nat 0 constantMessage
example : affineMessage.val.val.size ≤ 2 := size_le Nat 1 affineMessage
example : trivialMessage.val.val.size ≤ 1 := size_le (ZMod 1) 0 trivialMessage

#eval (show IO _ from do
  unless zeroMessage.val.val.size == 0 && constantMessage.val.val.size == 1 &&
      affineMessage.val.val.size == 2 && trivialMessage.val.val.size == 0 &&
      evaluate Nat 1 affineMessage 5 == 17 do
    throw (IO.userError "canonical length or ordinary message representation changed")
  pure (0,1,2,17))

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  unless (← collectAxioms ``size_le).all allowed.contains do
    throwError "unexpected canonical stored-length axiom"
  for name in #[``zeroMessage,``constantMessage,``affineMessage,``trivialMessage,
      ``Sumcheck.Impl.Representation.evaluate] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing ordinary canonical-message caller IR: {name}"

end RepresentationSizeTests
