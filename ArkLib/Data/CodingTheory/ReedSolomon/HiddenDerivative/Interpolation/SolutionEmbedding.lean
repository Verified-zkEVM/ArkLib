/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Certificates
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
/-!
# Embedding agreeing polynomials into bounded differential solutions

An interpolation certificate makes every sufficiently agreeing message polynomial a root of its
differential interpolant. This module packages that polynomial, unchanged, as a bounded solution
at the certificate's ambient degree. The construction is independent of how the interpolation
support was chosen, so both qualitative and weighted-support list bounds use the same embedding.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon

open HiddenDerivative ListDecoding Polynomial

noncomputable section

/-- Package a polynomial without changing its representation. -/
private theorem exists_boundedSolution_of_polynomial {F : Type*} [CommSemiring F] {d D : ℕ}
    (Q : DifferentialPolynomial F d) (P : Polynomial F)
    (hP : P ∈ Polynomial.degreeLT F (D + 1))
    (hQ : differentialSpecialization Q P = 0) :
    ∃ s : BoundedSolution Q D, s.polynomial = P :=
  ⟨⟨⟨P, hP⟩, hQ⟩, rfl⟩

/-- An agreeing message has a bounded-solution representative with the same polynomial. -/
theorem HiddenDerivativeInterpolationCertificate.exists_solution
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction : HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received)
    (p : agreeingPolynomials domain k A received) :
    ∃ solution : BoundedSolution construction.interpolant (construction.ambientDim - 1),
      solution.polynomial = (p.1 : Polynomial (ZMod q)) := by
  have hK : k ≤ (construction.ambientDim - 1) + 1 := by
    have := construction.order_lt_degree
    have := construction.messageDim_le
    omega
  exact exists_boundedSolution_of_polynomial construction.interpolant (p.1 : Polynomial (ZMod q))
    (Polynomial.degreeLT_mono hK p.1.property)
    (construction.specializes_to_zero p.1 p.property)

/-- Keep the original polynomial while viewing an agreeing message as a differential root. -/
def HiddenDerivativeInterpolationCertificate.solutionEmbedding
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    agreeingPolynomials domain k A received ↪
      BoundedSolution construction.interpolant (construction.ambientDim - 1) where
  toFun p := (construction.exists_solution p).choose
  inj' := by
    intro p p' h
    apply Subtype.ext
    apply Subtype.ext
    have hp := (construction.exists_solution p).choose_spec
    have hp' := (construction.exists_solution p').choose_spec
    exact hp.symm.trans ((congrArg BoundedSolution.polynomial h).trans hp')

end

end ReedSolomon
