/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Symbolic
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve

/-!
# First-order polynomial-curve certificate data

The received word is now a polynomial in the challenge at each domain point. A single
primitive equation is chosen before the challenge, candidate polynomial, and extension
field. Its nonzero specialization vanishes on every candidate with enough agreements.

The structure stores the primitive equation, finite support, local constraints, and soundness
after every extension-field challenge. The shifted graded constructor in `CurveFinite` produces
this data from an executable source/row surplus. Geometric exceptional-set counting is a separate
transfer.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve

noncomputable section

variable {F : Type*} [Field F]

/-- One primitive equation with support and specialization soundness on a polynomial curve. -/
structure FirstOrderCurveCertificate {n N : ℕ} (D A m M μ k h : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1) where
  coefficients : Fin N → F[X]
  Q : DifferentialPolynomial F[X] 1
  eq_interpolant : Q = interpolant columns coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h
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
