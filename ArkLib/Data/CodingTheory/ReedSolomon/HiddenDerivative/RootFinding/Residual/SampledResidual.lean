/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.SampledCoefficients
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Step
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
/-!
# Scalar-sample refinement of the concrete residual

A centered prefix is sampled at `u`, but the differential equation's independent variable is
`center+u`. Under the ambient degree and strict weighted-degree budgets, `L` distinct samples
recover every residual coefficient through a Vandermonde solve. The same samples suffice for
the complete zero-residual check.

This connects the existing concrete residual to the proposed scalar-evaluation implementation;
sampling, coefficient preparation, and matrix solving still need executable costed consumers.
No regularity, characteristic, or rate assumption is hidden in these algebraic identities.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open PolynomialDifferential
open Polynomial CompPoly
open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F] {r D L : ℕ}

/-- A scalar sample evaluates the original independent variable at the translated point. -/
theorem eval_effectiveResidual_eq_jet (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (u : F) :
    (effectiveResidual Q center P).toPoly.eval u =
      jetEvaluation (semanticEquation Q) (center + u) (polynomialJet u P.toPoly) := by
  rw [effectiveResidual_toPoly, ← taylor_differentialSpecialization, taylor_eval,
    eval_differentialSpecialization]
  have hjet : polynomialJet (u + center) (unshift center P) =
      (polynomialJet u P.toPoly : Fin (r + 1) → F) := by
    simp only [polynomialJet, unshift, hasseJet_taylor, add_neg_cancel_right]
  rw [hjet, add_comm u center]

/-- The scalar sampling budget applies to the concrete centered residual. -/
theorem natDegree_effectiveResidual_lt (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (hP : P.natDegree ≤ D)
    (hQ : differentialWeightedDegree D (semanticEquation Q) < L) :
    (effectiveResidual Q center P).toPoly.natDegree < L := by
  rw [effectiveResidual_toPoly, ← taylor_differentialSpecialization, natDegree_taylor]
  apply (natDegree_differentialSpecialization_le _ _ ?_).trans_lt hQ
  simpa only [unshift, natDegree_taylor, ← CPolynomial.natDegree_toPoly] using hP

/-- Any correct solve of the sampled residual system recovers its actual coefficient vector. -/
theorem effectiveResidual_coefficients_of_samples (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (hP : P.natDegree ≤ D)
    (hQ : differentialWeightedDegree D (semanticEquation Q) < L)
    (points : Fin L ↪ F) (coefficients : Fin L → F)
    (hsolve : Matrix.vandermonde (fun i ↦ points i) *ᵥ coefficients =
      fun i ↦ jetEvaluation (semanticEquation Q) (center + points i)
        (polynomialJet (points i) P.toPoly)) :
    coefficients = fun j : Fin L ↦ (effectiveResidual Q center P).coeff j := by
  have h := Polynomial.coefficients_eq_of_vandermonde_solve points
    (effectiveResidual Q center P).toPoly (natDegree_effectiveResidual_lt Q center P hP hQ)
    coefficients (by simpa only [eval_effectiveResidual_eq_jet] using hsolve)
  simpa only [CPolynomial.coeff_toPoly] using h

/-- The full concrete residual vanishes exactly when its bounded set of scalar samples vanish.
A caller with a possibly over-degree initial prefix must perform its degree check first. -/
theorem effectiveResidual_eq_zero_iff_samples (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (hP : P.natDegree ≤ D)
    (hQ : differentialWeightedDegree D (semanticEquation Q) < L) (points : Fin L ↪ F) :
    effectiveResidual Q center P = 0 ↔
      ∀ i, jetEvaluation (semanticEquation Q) (center + points i)
        (polynomialJet (points i) P.toPoly) = 0 := by
  have hs := Polynomial.eq_zero_iff_samples_eq_zero points
    (effectiveResidual Q center P).toPoly (natDegree_effectiveResidual_lt Q center P hP hQ)
  simp only [eval_effectiveResidual_eq_jet] at hs
  constructor
  · intro h
    apply hs.mp
    simp [h, CPolynomial.toPoly_zero]
  · intro h
    apply CPolynomial.ringEquiv.injective
    rw [CPolynomial.ringEquiv_apply, CPolynomial.ringEquiv_apply]
    rw [CPolynomial.toPoly_zero]
    exact hs.mpr h

end
end ReedSolomon.HiddenDerivative
