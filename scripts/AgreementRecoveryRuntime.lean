/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Decoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Materialize
import Mathlib.Algebra.Field.ZMod

/-!
# Compiled finite-representation recovery checks

Run with `lake exe agreement-recovery-runtime`. These checks execute polynomial gcd splitting,
base-field interpolation, agreement filtering, and deduplication. In particular, an irreducible
quadratic modulus must work even though it has no root in the base field. The kernel proofs of
coverage and exactness are separate from these concrete runtime checks.
-/

namespace AgreementRecoveryRuntime

open CompPoly ReedSolomon.ListDecoding

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def domain : Fin 3 ↪ ZMod 5 where
  toFun i := i.val
  inj' := by decide

private def affine : Fin 3 → ZMod 5 := ![1, 2, 3]

private def corrupted : Fin 3 → ZMod 5 := ![1, 2, 0]

private def pair (h : CPolynomial (ZMod 5)) (a b : ZMod 5) :
    FiniteRepresentation (ZMod 5) :=
  ⟨h, [CPolynomial.C a, CPolynomial.C b]⟩

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"agreement recovery: {label}")

/-- Exercise nonlinear blocks, extension-only roots, repeated images, final filtering,
corrupted received values, and the zero-width reference branch. -/
def run : IO Unit := do
  let x : CPolynomial (ZMod 5) := CPolynomial.X
  let identity := RingHom.id (ZMod 5)
  let splitRoots := pair (x ^ 2 - 1) 1 1
  let extensionRoots := pair (x ^ 2 + CPolynomial.C 2) 1 1
  check "nonlinear stopped block" <|
    AgreementRecovery.decode identity domain affine 2 3 [splitRoots] == [[1, 1]]
  check "no base-field modulus roots" <|
    AgreementRecovery.decode identity domain affine 2 3 [extensionRoots] == [[1, 1]]
  check "repeated representation images" <|
    AgreementRecovery.decode identity domain affine 2 3 [splitRoots, extensionRoots] == [[1, 1]]
  check "empty representation root set" <|
    AgreementRecovery.decode identity domain affine 2 3 [pair 1 1 1] == []
  check "insufficient agreements" <|
    AgreementRecovery.decode identity domain corrupted 2 3 [splitRoots] == []
  let varying : FiniteRepresentation (ZMod 5) := ⟨x ^ 2 - 1, [1, x]⟩
  check "gcd separates parameter roots" <|
    AgreementRecovery.decode identity domain corrupted 2 2 [varying] == [[1, 1]]
  let allLines := [pair x 1 1, pair x 2 1, pair x 3 4]
  let actual := AgreementRecovery.decode identity domain corrupted 2 2 allLines
  let reference := PositionSubsetDecoder.run domain corrupted 2 2
  check "all three interpolants" <| actual.length == 3
  check "reference agreement list" <|
    actual.all (fun cs => reference.contains cs) && reference.all (fun cs => actual.contains cs)
  check "zero-width reference" <| PositionSubsetDecoder.run domain affine 0 0 == [[]]
  check "threshold exceeds word length" <|
    PositionSubsetDecoder.run domain affine 2 4 == []
  check "constant decoding uses received-value frequencies" <|
    PositionSubsetDecoder.run domain (![2, 2, 3] : Fin 3 → ZMod 5) 1 2 == [[2]]
  check "leading zero padding" <|
    AgreementRecovery.decode identity domain (fun _ => 2) 2 3 [pair x 0 2] == [[0, 2]]
  check "zero polynomial padding" <|
    AgreementRecovery.decode identity domain (fun _ => 0) 2 3 [pair x 0 0] == [[0, 0]]
  -- Q=(Y-X-1)(Y+X+1) has two regular branches at center zero. The one symbolic
  -- series must carry both, and gcd recovery selects the branch close to this word.
  let qx := CPoly.CMvPolynomial.X (0 : Fin 2) (R := ZMod 5)
  let qy := CPoly.CMvPolynomial.X (1 : Fin 2) (R := ZMod 5)
  let equation := qy ^ 2 - (qx + 1) ^ 2
  let lifted := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.regularLift?
    equation 0 (x ^ 2 - 1) 3
  match lifted with
  | none => throw (IO.userError "regular quotient lift unexpectedly rejected")
  | some series =>
    check "simultaneous quotient coefficients" <|
      series.coeff 0 == x && series.coeff 1 == x && series.coeff 2 == 0
    let representation := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.materialize
      (x ^ 2 - 1) 0 2 series
    check "lifted representation recovers affine message" <|
      AgreementRecovery.decode identity domain affine 2 3 [representation] == [[1, 1]]
  let shiftedLift := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.regularLift?
    equation 2 (x ^ 2 - CPolynomial.C 4) 2
  match shiftedLift with
  | none => throw (IO.userError "nonzero-center quotient lift unexpectedly rejected")
  | some series =>
    let representation := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.materialize
      (x ^ 2 - CPolynomial.C 4) 2 2 series
    check "nonzero center shifts back correctly" <|
      AgreementRecovery.decode identity domain affine 2 3 [representation] == [[1, 1]]
  let linear := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.materialize
    (x - 1) 0 2 (CPolynomial.C x + CPolynomial.X)
  check "linear modulus reduces constant parameter" <|
    linear.coefficients == [1, 1]
  check "singular slope rejects" <|
    (ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.regularLift?
      (qy ^ 2) 0 x 2).isNone
  IO.println "Agreement recovery runtime checks passed."

end AgreementRecoveryRuntime

def main : IO Unit := AgreementRecoveryRuntime.run
