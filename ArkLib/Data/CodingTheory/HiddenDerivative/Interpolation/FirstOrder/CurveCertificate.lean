/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve

/-!
# First-order curve certificates

This module packages primitive first-order differential equations supported in the finite
first-order space, with local constraints and specialization soundness along received polynomial
curves.

## Main statements

* `FirstOrderCurveCertificate`: a primitive interpolant with bounded support and uniform
  specialization soundness along a received polynomial curve.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

/-- A primitive first-order interpolant with support and specialization soundness along a
received polynomial curve. -/
structure FirstOrderCurveCertificate {n N : ℕ} (D A m M μ k h : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1) where
  coefficients : Fin N → F[X]
  Q : DifferentialPolynomial F[X] 1
  eq_interpolant : Q = SourceColumn.interpolant columns coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (Q.coeff u).natDegree ≤ h
  support : Q ∈ firstOrderSpace F[X] D A m M μ
  firstJetDegree_le : ∀ u ∈ Q.support, firstJetExponent u ≤ M
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = (w i).eval₂ ι z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

end

end ReedSolomon.HiddenDerivative
