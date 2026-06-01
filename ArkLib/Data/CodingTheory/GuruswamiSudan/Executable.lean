/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic

import CompPoly.Bivariate.GuruswamiSudan

/-!
# Executable Guruswami-Sudan Decoder

ArkLib integration layer for the executable CompPoly Guruswami-Sudan core.
The decoder uses CompPoly's packed runtime formats, and correctness statements
are collected in `ArkLib.Data.CodingTheory.GuruswamiSudan.Correctness`.
-/

namespace GuruswamiSudan

/-- Certificate that executable parameters are valid for `(k, n, e)`. -/
structure GSParamCert
    (k n e : Nat)
    (params : CompPoly.GuruswamiSudan.GSExecParams) : Prop where
  messageDegree_eq :
    params.interp.messageDegree = k
  radius_eq :
    params.radius = e
  multiplicity_pos :
    0 < params.interp.multiplicity
  interpolation_capacity :
    numVars k params.interp.weightedDegreeBound >
      numConstraints n params.interp.multiplicity
  interpolation_witness_exists :
    ∀ {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F],
      (points : Array (F × F)) →
      points.size = n →
        ∃ Q, CompPoly.GuruswamiSudan.ValidInterpolationWitness points params.interp Q
  enough_agreement_bound :
    params.interp.weightedDegreeBound <
      params.interp.multiplicity * (n - e)

/-- ArkLib Johnson-radius condition for selector completeness. -/
def JohnsonSpecCondition (k n e : Nat) : Prop :=
  (e : ℝ) < (n : ℝ) - Real.sqrt (((k : ℝ) + 1) * (n : ℝ))

/-- Pure integer check matching the numeric fields of `GSParamCert`. -/
def paramsPassIntegerChecks
    (k n e : Nat)
    (params : CompPoly.GuruswamiSudan.GSExecParams) : Bool :=
  decide (params.interp.messageDegree = k) &&
    decide (params.radius = e) &&
      decide (0 < params.interp.multiplicity) &&
        decide (numVars k params.interp.weightedDegreeBound >
          numConstraints n params.interp.multiplicity) &&
          decide (params.interp.weightedDegreeBound <
            params.interp.multiplicity * (n - e))

/-- Constructor for executable parameters from multiplicity and weighted-degree bound. -/
def execParamsOfMultiplicityAndDegree
    (k e multiplicity weightedDegreeBound : Nat) :
    CompPoly.GuruswamiSudan.GSExecParams :=
  { interp :=
      { messageDegree := k
        multiplicity := multiplicity
        weightedDegreeBound := weightedDegreeBound }
    radius := e }

/-- Bounded, purely integer parameter search. -/
def searchParamsUpTo
    (maxMultiplicity maxWeightedDegree k n e : Nat) :
    Option CompPoly.GuruswamiSudan.GSExecParams :=
  (List.range' 1 maxMultiplicity).findSome? fun multiplicity =>
    match (List.range (maxWeightedDegree + 1)).find? fun weightedDegreeBound =>
        paramsPassIntegerChecks k n e
          (execParamsOfMultiplicityAndDegree k e multiplicity weightedDegreeBound) with
    | some weightedDegreeBound =>
        some (execParamsOfMultiplicityAndDegree k e multiplicity weightedDegreeBound)
    | none => none

/-- Parameter selector for the selector-backed executable decoder. -/
structure GSParamSelector where
  toCompPolySelector : CompPoly.GuruswamiSudan.GSParamSelector
  sound :
    ∀ {k n e params},
      toCompPolySelector.choose k n e = some params →
        GSParamCert k n e params
  complete :
    ∀ {k n e},
      JohnsonSpecCondition k n e →
        ∃ params,
          toCompPolySelector.choose k n e = some params ∧
            GSParamCert k n e params

/-- Certificate for using bounded integer search as a parameter selector. -/
structure GSBoundedSearchCert (maxMultiplicity maxWeightedDegree : Nat) : Prop where
  sound :
    ∀ {k n e params},
      searchParamsUpTo maxMultiplicity maxWeightedDegree k n e = some params →
        GSParamCert k n e params
  complete :
    ∀ {k n e},
      JohnsonSpecCondition k n e →
        ∃ params,
          searchParamsUpTo maxMultiplicity maxWeightedDegree k n e = some params ∧
            GSParamCert k n e params

/-- Parameter selector backed by bounded integer search and a proof certificate. -/
def boundedSearchParamSelector
    {maxMultiplicity maxWeightedDegree : Nat}
    (cert : GSBoundedSearchCert maxMultiplicity maxWeightedDegree) :
    GSParamSelector where
  toCompPolySelector :=
    { choose := searchParamsUpTo maxMultiplicity maxWeightedDegree }
  sound := cert.sound
  complete := cert.complete

end GuruswamiSudan
