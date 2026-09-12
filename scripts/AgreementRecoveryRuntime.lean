/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Decoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Materialize
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryQuotientDecoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.RationalRepresentationDecoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ComputedTaylorMap
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryInterpolatedDecoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ConstantDecoder
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SquareSystemDecoder
import ArkLib.ToCompPoly.Bivariate.Content
import ArkLib.Data.Polynomial.NonvanishingSearch
import ArkLib.Data.FiniteField.Candidates
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputablePool
import ArkLib.Data.Polynomial.SquarefreeSupport
import ArkLib.Data.Polynomial.BatchRemainder
import ArkLib.Data.Polynomial.Rojas.AffineCover
import ArkLib.Data.Polynomial.Rojas.SpecializationFamily
import ArkLib.Data.Polynomial.UnivariateRepresentation.FromRaw
import ArkLibTest.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerFoundations
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
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

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

/-- A two-variable linear fixture backend for testing the composed call path.
It derives both coordinates from the supplied rows by Cramer's rule. This runtime fixture is
only used on affine-linear systems and is not the missing general sparse toric solver. -/
private def linearFixtureBackend :
    ArkLib.Rojas.AffineSolver.TorusBackend (F := ZMod 5) (s := 2) := fun equations =>
  match equations with
  | [first, second] =>
      let c := CPoly.CMvPolynomial.eval ![0, 0] first
      let d := CPoly.CMvPolynomial.eval ![0, 0] second
      let a := CPoly.CMvPolynomial.eval ![1, 0] first - c
      let b := CPoly.CMvPolynomial.eval ![0, 1] first - c
      let e := CPoly.CMvPolynomial.eval ![1, 0] second - d
      let f := CPoly.CMvPolynomial.eval ![0, 1] second - d
      let determinant := a * f - b * e
      if determinant == 0 then [] else
        [⟨CPolynomial.X, 1,
          [CPolynomial.C ((b * d - c * f) / determinant),
            CPolynomial.C ((c * e - a * d) / determinant)]⟩]
  | _ => []

/-- Exercise nonlinear blocks, extension-only roots, repeated images, final filtering,
corrupted received values, and the zero-width reference branch. -/
def run : IO Unit := do
  ArkLibTest.TowerFoundations.run
  check "constant-message balanced frequency map" <|
    ConstantDecoder.decode compare 3 ([4, 2, 4, 4, 2, 7] : List Nat) == [[4]]
  let x : CPolynomial (ZMod 5) := CPolynomial.X
  check "ordinary interpolation through Newton and recovery" <|
    OrdinaryInterpolatedDecoder.run 5 (RingHom.id (ZMod 5)) domain affine 2 3
      ⟨2, 1, 2⟩ 0 == [[1, 1]]
  let withContent : CompPoly.CBivariate (ZMod 5) :=
    CPolynomial.C (x + 1) * (CPolynomial.X + 2)
  check "ordinary bivariate content identifies common X factor" <|
    CompPoly.CBivariate.yContent withContent == x + 1
  check "ordinary primitive part divides out common X factor" <|
    CompPoly.CBivariate.primitivePartY withContent == CPolynomial.X + 2
  let centers := ArkLib.FiniteFieldCandidates.primeFieldPrefix (ZMod 5) 3
  check "batched discriminant candidate search" <|
    CPolynomial.findNonzeroEvaluation? (.subproduct (ZMod 5) .naive .remainderOnly)
      (x * (x - 1)) centers == some 2
  check "identically zero discriminant has no passing center" <|
    (CPolynomial.findNonzeroEvaluation? (.horner (ZMod 5)) 0 centers).isNone
  match OrdinaryInterpolation.run (OrdinaryInterpolation.receivedPoints domain affine)
      ⟨2, 1, 2⟩ with
  | none => throw (IO.userError "ordinary multiplicity interpolation unexpectedly rejected")
  | some Q =>
      check "computed interpolant contains affine message" <|
        CompPoly.CBivariate.composeY Q (x + 1) == 0
  -- The batch includes a quadratic, a repeated leaf, a unit modulus and an odd leaf count.
  -- Comparing full remainders checks order and multiplicity, beyond scalar root evaluations.
  let moduli := [x ^ 2 + 2, x - 1, 1, x ^ 2 + 2, x ^ 3 + x + 1]
  let residual := x ^ 9 + 3 * x ^ 4 + 2
  check "arbitrary-factor remainder tree" <|
    CPolynomial.BatchRemainder.remainders .naive .remainderOnly residual moduli ==
      moduli.map (residual.modByMonic ·)
  check "empty remainder forest" <|
    (CPolynomial.BatchRemainder.remainders .naive .naive residual []).isEmpty
  -- From roots 1,2,3, the denominator rejects 1 and the tail equation retains only 2.
  -- The numerator U+1 divided by U−1 then specializes to 3 at the retained root.
  let rational : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    ⟨(x - 1) * (x - 2) * (x - 3), x - 1, [x + 1]⟩
  check "filter invert and materialize" <|
    match ArkLib.UnivariateRepresentation.postprocess? rational [x - 2] with
    | none => false
    | some out => out.modulus == x - 2 && out.coordinates == [CPolynomial.C 3]
  let repeated : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    { rational with modulus := rational.modulus ^ 2 }
  check "normalize repeated eliminant before filtering" <|
    match ArkLib.UnivariateRepresentation.postprocessRaw? 5 repeated [x - 2] with
    | none => false
    | some out => out.modulus == x - 2 && out.coordinates == [CPolynomial.C 3]
  let identity := RingHom.id (ZMod 5)
  -- The raw Taylor map has two repeated parameter roots. Its tail U−1 retains only U=1.
  let taylorMap : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    ⟨(x ^ 2 - 1) ^ 2, 1, [x, x, x - 1]⟩
  check "rational Taylor map tail and normalization" <|
    match RationalRepresentationDecoder.fromRational? 5 0 2 taylorMap with
    | none => false
    | some r => r.modulus == x - 1 && r.coefficients == [1, 1]
  check "rational Taylor map shared decoding" <|
    RationalRepresentationDecoder.run 5 identity domain affine 0 2 3 [taylorMap] == [[1, 1]]
  let shiftedMap : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    ⟨x - 1, 1, [3, 1, 0]⟩
  check "rational Taylor map nonzero-center shift" <|
    RationalRepresentationDecoder.run 5 identity domain affine 2 2 3 [shiftedMap] == [[1, 1]]
  let impossibleTail : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    { taylorMap with numerators := [x, x, 1] }
  check "rational Taylor map empty tail locus" <|
    RationalRepresentationDecoder.run 5 identity domain affine 0 2 3 [impossibleTail] == []
  -- The solver denominator removes U=-1; the chart denominator removes U=0;
  -- and the Taylor tail retains U=1. The surviving branch is the message X+1.
  let rawJet : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    ⟨((x + 1) * x * (x - 1)) ^ 2, x + 1, [x * (x + 1)]⟩
  let jetVariable := CPoly.CMvPolynomial.X (0 : Fin 1) (R := ZMod 5)
  check "raw jet through chart to exact message" <|
    match TaylorChartMap.fromJet? 5 0 2 rawJet
        [jetVariable, jetVariable, jetVariable - 1] jetVariable with
    | none => false
    | some r => r.modulus == x - 1 && r.coefficients == [1, 1] &&
        AgreementRecovery.decode identity domain affine 2 3 [r] == [[1, 1]]
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
  -- Y' = 1 produces the affine Taylor family. All later numerator slots vanish, and
  -- selecting one agreement row plus the initial equation yields square systems in two jets.
  let derivativeEquation := CPoly.CMvPolynomial.X (2 : Fin 3) (R := ZMod 5) - 1
  let secondNumerator :=
    ReedSolomon.HiddenDerivative.SquareSystems.computableRationalTaylorNumerator
      0 derivativeEquation 2
  check "computed first higher Taylor numerator" <| secondNumerator == 0
  let rawAffineJet : ArkLib.UnivariateRepresentation.MapData (F := ZMod 5) :=
    ⟨x - 1, 1, [x, 1]⟩
  check "computed equation chart through final recovery" <|
    ComputedTaylorMap.run 5 identity domain affine 0 derivativeEquation 3 6 2 3
      [rawAffineJet] == [[1, 1]]
  check "square enumeration through affine fixture and shared recovery" <|
    SquareSystemDecoder.run 5 identity domain affine 0 derivativeEquation 3 6 2 3
      (by decide) linearFixtureBackend [0, 1, 2] == [[1, 1]]
  -- Y' = Y needs several nonzero recurrence steps. At jet (1,1), the fourth coefficient
  -- is 1/4! = 4 in F₅. This checks shared-prefix indexing beyond the first higher slot.
  let exponentialEquation := CPoly.CMvPolynomial.X (2 : Fin 3) (R := ZMod 5) -
    CPoly.CMvPolynomial.X (1 : Fin 3)
  let taylorTable := ReedSolomon.HiddenDerivative.SquareSystems.computableRationalTaylorTable
    0 exponentialEquation 5
  check "shared Taylor table reaches fourth coefficient" <|
    taylorTable.size == 5 && CPoly.CMvPolynomial.eval (R := ZMod 5) ![1, 1]
      (taylorTable[4]'(by simp [taylorTable])) == 4
  let squareSystems := ReedSolomon.HiddenDerivative.SquareSystems.squareSystemsFromEquation
    0 derivativeEquation 3 6 2 3 (by decide) domain affine
  check "computed square-system family includes affine solution" <|
    decide (∃ rows ∈ squareSystems,
      ∀ i, CPoly.CMvPolynomial.eval ![1, 1] (rows i) = 0)
  let qx := CPoly.CMvPolynomial.X (0 : Fin 2) (R := ZMod 5)
  let qy := CPoly.CMvPolynomial.X (1 : Fin 2) (R := ZMod 5)
  let family := ArkLib.Rojas.specializationFamily (qx + qy) ![2] 1
  check "computed Rojas base and coordinate shifts" <|
    family.eliminant == x + CPolynomial.C 2 &&
      family.minus 0 == x + 1 && family.plus 0 == x + CPolynomial.C 3 &&
      family.shiftedEliminants.length == 2
  check "affine chart substitution" <|
    CPoly.CMvPolynomial.eval₂ (RingHom.id (ZMod 5)) ![1, 2]
      (ArkLib.Rojas.AffineCover.translatePolynomial 2 (qx * qy)) == 2
  let perturbation := CPolynomial.ofArray #[0, x + 1, x + 2]
  check "lowest perturbation coefficient" <|
    ArkLib.Rojas.lowestNonzeroCoefficient? perturbation == some (x + 1)
  let incomplete : ArkLib.Rojas.SpecializationCandidate (F := ZMod 5) :=
    ⟨1, x ^ 2 - 1, []⟩
  let complete : ArkLib.Rojas.SpecializationCandidate (F := ZMod 5) :=
    ⟨2, x ^ 2 - 1, [x ^ 2 - 1, x ^ 2 - 1]⟩
  check "Rojas guard rejects missing shifted eliminants" <|
    !ArkLib.Rojas.hasExpectedSupportDegree 5 1 2 incomplete
  check "Rojas deterministic full-family selection" <|
    match ArkLib.Rojas.selectSpecialization? 5 1 2 [incomplete, complete] with
    | none => false
    | some selected => selected.parameter == 2
  let equation := qy ^ 2 - (qx + 1) ^ 2
  let lifted := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.newtonLift?
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
  -- Precision 5 forces the guarded loop through 1→2→4→8. The nonlinear equation also
  -- requires updating the inverse at the new branch, not just adding a final coefficient.
  match ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.newtonLift?
      (qy ^ 2 - (qx ^ 4 + qx + 1) ^ 2) 0 (x ^ 2 - 1) 5 with
  | none => throw (IO.userError "Newton lift unexpectedly rejected")
  | some series =>
    check "three Newton precision doublings" <|
      series == CPolynomial.ofArray #[x, x, 0, 0, x]
  let shiftedLift := ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.newtonLift?
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
    (ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.newtonLift?
      (qy ^ 2) 0 x 2).isNone
  check "ordinary decoder computes its own modulus" <|
    OrdinaryQuotientDecoder.run 5 identity domain affine 2 3 equation 0 == [[1, 1]]
  check "ordinary decoder at nonzero center" <|
    OrdinaryQuotientDecoder.run 5 identity domain affine 2 3 equation 2 == [[1, 1]]
  check "repeated-root slice removes singular branches" <|
    OrdinaryQuotientDecoder.run 5 identity domain affine 2 3 ((qy-qx-1)^2) 0 == []
  check "zero slice is rejected" <|
    OrdinaryQuotientDecoder.run 5 identity domain affine 2 3 (qx * qy) 0 == []
  let x2 : CPolynomial (ZMod 2) := CPolynomial.X
  check "inseparable squarefree support" <|
    CPolynomial.squarefreeSupport 2 ((x2 + 1) ^ 2) == x2 + 1
  check "mixed separable and inseparable factors" <|
    CPolynomial.squarefreeSupport 2 (x2 ^ 2 * (x2 + 1)) == x2 * (x2 + 1)
  check "overlapping support uses lcm" <|
    CPolynomial.squarefreeSupport 2 (x2 ^ 3) == x2
  let irreducible := x2 ^ 2 + x2 + 1
  check "geometric support without base-field roots" <|
    CPolynomial.squarefreeSupport 2 (irreducible ^ 2) == irreducible
  check "nonmonic support normalization" <|
    CPolynomial.squarefreeSupport 5 (CPolynomial.C 2 * (x + 1) ^ 2) == x + 1
  check "zero support policy" <|
    CPolynomial.squarefreeSupport 5 (0 : CPolynomial (ZMod 5)) == 0
  IO.println "Agreement recovery runtime checks passed."

end AgreementRecoveryRuntime

def main : IO Unit := AgreementRecoveryRuntime.run
