/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Basis
/-!
# Executable eligibility for first-order rate certificates

This file connects the field-generic symbolic rate certificate to the executable interpolation
machine. Keeping this adapter separate prevents the mathematical certificate constructor from
depending on machine semantics.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

noncomputable section

set_option autoImplicit false

universe u

/-- A capped first-order support is eligible for the executable support whose strict jet cutoff
is one larger than the weak cap. -/
theorem firstOrderSpace_eligibleWithBudget
    {F : Type*} [Field F] {D A m M μ : ℕ} {Q : DifferentialPolynomial F 1}
    (hQ : Q ∈ firstOrderSpace F D A m M μ) :
    NonzeroInterpolationMachine.EligibleWithBudget D m (μ + 1) A Q := by
  rw [NonzeroInterpolationMachine.eligibleWithBudget_iff]
  intro e he
  have h := mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQ e he)
  constructor
  · simpa [totalJetDegree, Finsupp.degree_eq_sum] using Nat.lt_succ_of_le h.2.1
  · simpa [exactInterpolationMonomialWeight, Finsupp.weight_apply,
      Finsupp.sum_fintype, Fintype.sum_option, differentialWeight, mul_comm] using h.2.2

/-- The retained primitive equation remains nonzero after every base-field challenge. -/
theorem FirstOrderSymbolicCertificate.specialization_nonzero
    {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
    {centers : Fin n ↪ F} {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h centers f g columns)
    (z : F) : MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) z) cert.Q ≠ 0 :=
  (cert.specialization_sound (E := F) (RingHom.id F) z).1

/-- Every challenge specialization lies in the explicitly budgeted executable support. -/
theorem FirstOrderSymbolicCertificate.specialization_eligibleWithBudget
    {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
    {centers : Fin n ↪ F} {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h centers f g columns)
    (z : F) : NonzeroInterpolationMachine.EligibleWithBudget D m (μ + 1) A
      (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) z) cert.Q) := by
  apply firstOrderSpace_eligibleWithBudget (M := M)
  rw [mem_firstOrderSpace_iff]
  intro e he
  exact mem_firstOrderSpace_iff.mp cert.support e
    (MvPolynomial.support_map_subset _ cert.Q he)

/-- Every challenge specialization satisfies each actual local interpolation equation. By
definition, this proposition is the equality `localConstraintAt ... = 0`. -/
theorem FirstOrderSymbolicCertificate.specialization_satisfiesLocalConstraints
    {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
    {centers : Fin n ↪ F} {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h centers f g columns)
    (z : F) (i : Fin n) :
    SatisfiesLocalConstraints m (centers i) (f i + z * g i)
      (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) z) cert.Q) := by
  let φ := Polynomial.eval₂RingHom (RingHom.id F) z
  have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
    (receivedLine (f i) (g i)) cert.Q (cert.localConstraints i)
  change SatisfiesLocalConstraints m
    (Polynomial.eval₂ (RingHom.id F) z (Polynomial.C (centers i)))
    ((receivedLine (f i) (g i)).eval₂ (RingHom.id F) z)
      (MvPolynomial.map φ cert.Q) at hi
  simp only [Polynomial.eval₂_C, receivedLine, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_X] at hi
  simpa only [φ, RingHom.id_apply, mul_comm] using hi

/-- Specializing the retained line challenge gives an actual nonzero executable interpolant.
It is eligible for the finite budgeted support and satisfies every original local equation. -/
theorem FirstOrderSymbolicCertificate.exists_executableSpecialization
    {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
    {centers : Fin n ↪ F} {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h centers f g columns)
    (z : F) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧ NonzeroInterpolationMachine.EligibleWithBudget D m (μ + 1) A Q ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (f i + z * g i) Q := by
  let φ := Polynomial.eval₂RingHom (RingHom.id F) z
  refine ⟨MvPolynomial.map φ cert.Q, cert.specialization_nonzero z,
    cert.specialization_eligibleWithBudget z, ?_⟩
  exact cert.specialization_satisfiesLocalConstraints z

end

end ReedSolomon.HiddenDerivative
