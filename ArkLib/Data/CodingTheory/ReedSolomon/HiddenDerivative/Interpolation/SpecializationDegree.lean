/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Index
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
/-!
# Specialization degree of exact interpolation polynomials

This file joins the exact interpolation support inequality to the generic differential-
specialization degree theorem.  Every polynomial represented by the exact coefficient space has
specialization degree strictly below `m * A` at every polynomial of degree at most `D`.

The exact support predicate and its `(1, D, D - 1, ..., D - d)` weighted-degree consequence are
proved in `InterpolationIndex.lean`.  The generic specialization estimate is proved in
`RootFinding/SpecializationDegree.lean`; that proof is the coefficient-ring-general form of the
authorized `kz99/rs-ld-mca` source argument in
`RSListDecoding/Lemmas/GlobalBudgets.lean`, at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`.  The two integration theorems below are
ArkLib-specific adapters, not a further source port.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {D A d m M W : ℕ}

/-- Exact interpolation support gives the strict specialization bound at every polynomial of
degree at most `D`.  Positivity is necessary because the zero polynomial has natural degree zero.
-/
theorem natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace
    [CommSemiring F] (hbudget : 0 < m * A) (hdD : d < D)
    {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (P : F[X]) (hP : P.natDegree ≤ D) :
    (differentialSpecialization Q P).natDegree < m * A :=
  (natDegree_differentialSpecialization_le Q P hP).trans_lt
    (differentialWeightedDegree_lt_of_mem_exactInterpolationSpace hbudget hdD hQ)

/-- Coefficient-facing form of the exact specialization bound.  This is the interface consumed by
the interpolation kernel and the downstream root-finding assembly. -/
theorem natDegree_differentialSpecialization_exactInterpolationPolynomial_lt
    [CommSemiring F] (hbudget : 0 < m * A) (hdD : d < D)
    (c : ExactInterpolationCoefficients F D A d m M W hdD)
    (P : F[X]) (hP : P.natDegree ≤ D) :
    (differentialSpecialization
      (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d) P).natDegree <
        m * A := by
  exact natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace
    hbudget hdD (exactInterpolationPolynomial hdD c).property P hP

end

end ReedSolomon.HiddenDerivative
