/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.EquationChecks
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Run
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance checks for executable hidden-derivative equation certification
-/

open _root_.ReedSolomon.ListDecoding.HiddenDerivativeDecoder

namespace ArkLibTest.ReedSolomon.ListDecoding.HiddenDerivativeDecoder

local instance primeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private def input : Input (ZMod 7) 3 where
  domain := ⟨fun i ↦ i.val, by
    intro a b hab
    apply Fin.ext
    have hvals := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt (by omega : (a : Nat) < 7),
      ZMod.val_natCast_of_lt (by omega : (b : Nat) < 7)] using hvals⟩
  received := fun _ ↦ 0
  k := 2
  agreement := 3
  characteristic := 7

private def equationOptions : Options where
  order := 1
  multiplicity := 1
  jetDegree := 2
  xDegreeFactor := 2

private def boundaryEquation : SuppliedEquation (ZMod 7) equationOptions where
  polynomial := CPoly.CMvPolynomial.monomial #m[6, 1, 1] 1

private def excessiveXEquation : SuppliedEquation (ZMod 7) equationOptions where
  polynomial := CPoly.CMvPolynomial.monomial #m[7, 0, 0] 1

private def excessiveJetEquation : SuppliedEquation (ZMod 7) equationOptions where
  polynomial := CPoly.CMvPolynomial.monomial #m[0, 2, 1] 1

private def zeroEquation : SuppliedEquation (ZMod 7) equationOptions where
  polynomial := 0

/-- Reflection exposes semantic nonzeroness and the semantic support bounds. -/
example (hpass : boundaryEquation.boundsPass (n := 3) = true) :
    ReedSolomon.HiddenDerivative.semanticEquation boundaryEquation.polynomial ≠ 0 ∧
      boundaryEquation.WithinBounds (n := 3) :=
  (SuppliedEquation.boundsPass_eq_true_iff boundaryEquation).mp hpass

private def supportOptions : Options where
  order := 0
  multiplicity := 1
  jetDegree := 1
  xDegreeFactor := 1

private def validCertificate : SupportCertificate where
  vectors := [[0, 0], [1, 0], [2, 0], [0, 1]]

private def emptyCertificate : SupportCertificate where
  vectors := []

private def duplicateCertificate : SupportCertificate where
  vectors := [[0, 0], [0, 0], [1, 0], [0, 1]]

private def shortCertificate : SupportCertificate where
  vectors := [[0], [1, 0], [2, 0], [0, 1]]

/-- The explicit prime-field size contract holds for the concrete test field. -/
example : PrimeFieldSized (ZMod 7) := by
  simp [PrimeFieldSized, ZMod.card, ZMod.ringChar_zmod_n]

/-- Executed by the compiled agreement-recovery runtime suite. -/
def run : IO Unit := do
  unless boundaryEquation.boundsPass (n := 3) do
    throw (IO.userError "equation check 1 failed: boundary degrees")
  unless !excessiveXEquation.boundsPass (n := 3) do
    throw (IO.userError "equation check 2 failed: excessive X degree")
  unless !excessiveJetEquation.boundsPass (n := 3) do
    throw (IO.userError "equation check 3 failed: excessive total jet degree")
  unless !zeroEquation.boundsPass (n := 3) do
    throw (IO.userError "equation check 4 failed: zero equation")
  let rowCount := Explainer.rowCount supportOptions.order
    (validCertificate.support supportOptions)
    (Explainer.receivedPoints input.domain input.received)
  unless rowCount == 3 do
    throw (IO.userError "equation check 5 failed: compact row count")
  unless validCertificate.check input supportOptions do
    throw (IO.userError "equation check 6 failed: valid support")
  unless !emptyCertificate.check input supportOptions do
    throw (IO.userError "equation check 7 failed: empty support")
  unless !duplicateCertificate.check input supportOptions do
    throw (IO.userError "equation check 8 failed: duplicate support")
  unless !shortCertificate.check input supportOptions do
    throw (IO.userError "equation check 9 failed: short support vector")
  unless inputArithmeticPass input do
    throw (IO.userError "equation check 10 failed: input arithmetic")
  unless optionsArithmeticPass supportOptions do
    throw (IO.userError "equation check 11 failed: option arithmetic")
  unless decide (prescribedGuardsPass 7 7 3 2 supportOptions) do
    throw (IO.userError "equation check 12 failed: prescribed guards")
  unless decide (¬ fallbackRequired (ZMod 7) input supportOptions) do
    throw (IO.userError "equation check 13 failed: unexpected fallback")
  unless dispatch (F := ZMod 7) input supportOptions == .symbolic do
    throw (IO.userError "equation check 14 failed: symbolic dispatch")
  unless dispatch (F := ZMod 7) ({ input with agreement := 4 }) supportOptions ==
      .impossibleAgreement do
    throw (IO.userError "equation check 15 failed: impossible agreement priority")
  unless dispatch (F := ZMod 7) ({ input with k := 1 }) supportOptions == .constant do
    throw (IO.userError "equation check 16 failed: constant priority")
  match construct input supportOptions validCertificate with
  | .error _ =>
      throw (IO.userError "equation check 17 failed: valid construction rejected")
  | .ok equation =>
      unless equation.boundsPass (n := 3) do
        throw (IO.userError "equation check 18 failed: constructed bounds")

end ArkLibTest.ReedSolomon.ListDecoding.HiddenDerivativeDecoder
