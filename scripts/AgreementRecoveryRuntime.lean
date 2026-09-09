/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Decoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
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
  IO.println "Agreement recovery runtime checks passed."

end AgreementRecoveryRuntime

def main : IO Unit := AgreementRecoveryRuntime.run
