/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.DirectRegularIteration
import Mathlib.Algebra.Field.ZMod

/-!
# Compiled regular-lifting regression checks

Run with `lake exe regular-lift-runtime`. These concrete vectors exercise CompPoly's executable
representation, including operations with opaque kernel definitions. They are runtime tests, not
proofs by native evaluation and not complexity certificates. The library's semantic refinement and
residual-invariant theorems remain kernel checked independently.
-/

namespace RegularLiftRuntime

open CompPoly ReedSolomon.HiddenDerivative

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def derivativeMinusX : CPoly.CMvPolynomial 3 (ZMod 5) :=
  CPoly.CMvPolynomial.X (2 : Fin 3) - CPoly.CMvPolynomial.X (0 : Fin 3)

private def constantOnePrefix : CPolynomial (ZMod 5) := effectiveInitialPrefix ![1, 0]

private def forcedQuadratic : CPolynomial (ZMod 5) :=
  effectiveRegularCandidate 1 1 constantOnePrefix 3

private def derivativeMinusValue : CPoly.CMvPolynomial 3 (ZMod 5) :=
  CPoly.CMvPolynomial.X (2 : Fin 3) - CPoly.CMvPolynomial.X (1 : Fin 3)

private def linearOnePrefix : CPolynomial (ZMod 5) := effectiveInitialPrefix ![1, 1]

private def locallyForcedQuadratic : CPolynomial (ZMod 5) :=
  effectiveRegularCandidate 1 1 linearOnePrefix 3

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"regular lifting: {label}")

/-- Distinguish true roots from locally valid prefixes and test the reported partial counters. -/
def run : IO Unit := do
  check "regular coefficient" <|
    effectiveRegularCoefficients derivativeMinusX 0 constantOnePrefix 1 == {3}
  check "quadratic coefficients" <|
    [forcedQuadratic.coeff 0, forcedQuadratic.coeff 1, forcedQuadratic.coeff 2] == [1, 0, 3]
  check "zero residual" <| effectiveResidual derivativeMinusX 0 forcedQuadratic == 0
  check "locally forced coefficient" <|
    effectiveRegularCoefficients derivativeMinusValue 0 linearOnePrefix 1 == {3}
  check "locally forced polynomial" <|
    [locallyForcedQuadratic.coeff 0, locallyForcedQuadratic.coeff 1,
      locallyForcedQuadratic.coeff 2] == [1, 1, 3]
  check "nonzero higher residual" <|
    [(effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 0,
      (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 1,
      (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 2] == [0, 0, 2]
  check "retain true solution" <|
    effectiveRegularSolutions derivativeMinusX 0 constantOnePrefix 2 == {forcedQuadratic}
  check "reject locally valid false solution" <|
    effectiveRegularSolutions derivativeMinusValue 0 linearOnePrefix 2 == ∅
  check "one coefficient scan" <|
    effectiveRegularTestCount derivativeMinusX 0 constantOnePrefix 2 == 5
  check "no requested stage" <|
    effectiveRegularTestCount derivativeMinusX 0 constantOnePrefix 1 == 0
  check "first Hasse derivative" <| (effectiveHasseRun 1 forcedQuadratic).result == CPolynomial.X
  check "first derivative partial counters" <|
    [(effectiveHasseRun 1 forcedQuadratic).additions,
      (effectiveHasseRun 1 forcedQuadratic).multiplications,
      (effectiveHasseRun 1 forcedQuadratic).visited] == [6, 3, 3]
  check "third Hasse derivative" <| (effectiveHasseRun 3 forcedQuadratic).result == 0
  check "zero result does not mean zero work" <|
    [(effectiveHasseRun 3 forcedQuadratic).additions,
      (effectiveHasseRun 3 forcedQuadratic).multiplications,
      (effectiveHasseRun 3 forcedQuadratic).visited] == [15, 3, 3]
  check "direct regular coefficient" <|
    effectiveDirectRegularCoefficient derivativeMinusX 0 constantOnePrefix 1 == some 3
  let zeroEquation : CPoly.CMvPolynomial 3 (ZMod 5) := 0
  check "zero equation has unavailable direct solve" <|
    effectiveDirectRegularCoefficient zeroEquation 0 constantOnePrefix 1 == none
  check "unavailable solve may have every coefficient as root" <|
    effectiveRegularCoefficients zeroEquation 0 constantOnePrefix 1 == Finset.univ
  let xEquation : CPoly.CMvPolynomial 3 (ZMod 5) := CPoly.CMvPolynomial.X (0 : Fin 3)
  check "nonzero constant residual has unavailable direct solve" <|
    effectiveDirectRegularCoefficient xEquation 0 constantOnePrefix 1 == none
  check "unavailable solve may have no roots" <|
    effectiveRegularCoefficients xEquation 0 constantOnePrefix 1 == ∅
  check "direct iteration produces the forced quadratic" <|
    directRegularIteration derivativeMinusX 0 constantOnePrefix 1 == some forcedQuadratic
  check "direct final filter retains genuine solution" <|
    directRegularSolution derivativeMinusX 0 ![1, 0] 2 == some forcedQuadratic
  check "direct local iteration can produce a nonsolution" <|
    directRegularIteration derivativeMinusValue 0 linearOnePrefix 1 == some locallyForcedQuadratic
  check "direct final filter rejects local nonsolution" <|
    directRegularSolution derivativeMinusValue 0 ![1, 1] 2 == none
  let derivative : CPoly.CMvPolynomial 3 (ZMod 5) := CPoly.CMvPolynomial.X (2 : Fin 3)
  check "degree below jet accepts constant" <|
    directRegularSolution derivative 0 ![1, 0] 0 == some constantOnePrefix
  check "degree below jet rejects linear" <|
    directRegularSolution (derivative - 1) 0 ![1, 1] 0 == none
  check "direct zero stages retain input" <|
    directRegularIteration derivative 0 linearOnePrefix 0 == some linearOnePrefix
  check "direct zero-slope failure" <|
    directRegularIteration zeroEquation 0 constantOnePrefix 1 == none
  check "direct failure propagates" <|
    directRegularIteration zeroEquation 0 constantOnePrefix 2 == none
  let translated := effectiveRegularCandidate 1 1 (effectiveInitialPrefix ![1, 2]) 3
  check "direct nonzero center" <|
    directRegularSolution derivativeMinusX 2 ![1, 2] 2 == some translated
  check "direct nonzero-center result agrees with exhaustive scan" <|
    (directRegularSolution derivativeMinusX 2 ![1, 2] 2).toFinset ==
      effectiveRegularSolutions derivativeMinusX 2 (effectiveInitialPrefix ![1, 2]) 2
  IO.println "Regular-lifting runtime checks passed (30 checks)."

end RegularLiftRuntime

def main : IO Unit := RegularLiftRuntime.run
