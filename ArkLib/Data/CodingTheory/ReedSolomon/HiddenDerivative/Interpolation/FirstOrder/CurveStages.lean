/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveSymbolic
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.JetPrefix

/-!
# Regular-stage coverage for finite first-order curve certificates

Interpolation constructs one equation before the challenge is sampled. Separant descent
then replaces its possibly singular solutions by regular solutions of a finite sequence
of equations. A single terminal obstruction accounts for all exceptional challenges in
this descent, with cardinality at most the original interpolation height.

## Reading the statements

The input is the actual finite curve certificate. Its nonvanishing and degree bounds are
derived from its fields. In positive characteristic only the total jet-degree cap enters
the descent condition; the challenge height can be larger than the characteristic.

The exceptional set is chosen before the candidate and its agreement positions, uniformly
over the supplied extension field. Outside it, every sufficiently agreeing candidate is
a regular root of one of the actual stages. Counting the regular roots and recovering
correlated tuples are the subsequent geometric steps.
-/

@[expose] public section

noncomputable section

open PolynomialDifferential Polynomial MvPolynomial

namespace ReedSolomon.HiddenDerivative.FirstOrderCurveCertificate

open SymbolicSeparantChain SymbolicReceivedInterpolation

universe u

variable {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
  {domain : Fin n ↪ F} {w : Fin n → F[X]} {columns : Fin N → SourceColumn 1}

/-- Uniform nonvanishing under specialization implies a nonzero symbolic equation. -/
theorem nonzero (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns) :
    cert.Q ≠ 0 := by
  intro hzero
  have hne := (cert.specialization_sound (RingHom.id F) 0).1
  rw [hzero, map_zero] at hne
  exact hne rfl

/-- The actual jet weight is bounded by the finite support cap. -/
theorem jetWeight_le (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns) :
    jetWeight cert.Q ≤ μ := by
  apply Finset.sup_le_iff.mpr
  intro u hu
  have hbound := cert.totalJetDegree_le u hu
  simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.weight_apply,
    Finsupp.sum_fintype] using hbound

/-- The actual first-derivative degree retains the asymmetric support cap. -/
theorem jetDegree_one_le
    (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns) :
    jetDegree cert.Q (1 : Fin 2) ≤ M := by
  change degreeOf (some (1 : Fin 2)) cert.Q ≤ M
  rw [degreeOf_eq_sup]
  apply Finset.sup_le
  intro u hu
  simpa [firstJetExponent, Finsupp.weight_apply, Finsupp.sum_fintype] using
    cert.firstJetDegree_le u hu

/-- Construct the derivative chain from the finite certificate. -/
theorem exists_separant_chain
    (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns)
    (hchar : ringChar F = 0 ∨ μ < ringChar F) :
    ∃ stages terminal, Chain cert.Q stages terminal := by
  apply exists_symbolic_chain cert.Q cert.nonzero
  exact hchar.imp_right (fun ht ↦ cert.jetWeight_le.trans_lt ht)

/-- A single height-bounded exceptional set gives regular-stage coverage for every candidate. -/
theorem exists_exceptional_stage_coverage
    (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns)
    {stages : List (Stage F[X] 1)} {terminal : DifferentialPolynomial F[X] 1}
    (hc : Chain cert.Q stages terminal) {E : Type u} [Field E] (ι : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ h ∧
      ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
        P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1)
              stage.2) P ≠ 0 := by
  obtain ⟨exceptional, hcard, hcover⟩ :=
    hc.exists_exceptional_regular_coverage cert.challengeDegree_le ι
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz indices P hdegree hagree hvalues
  exact hcover z hz P ((cert.specialization_sound ι z).2 indices P hdegree hagree hvalues)

end ReedSolomon.HiddenDerivative.FirstOrderCurveCertificate
