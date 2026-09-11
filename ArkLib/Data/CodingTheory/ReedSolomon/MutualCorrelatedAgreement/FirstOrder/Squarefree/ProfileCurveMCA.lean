/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.RetainedCurveBounds

/-!
# Retained squarefree MCA from verified finite profiles

A `LineProfile` records both a scalar interpolation row and its actual polynomial-curve batching
degree.  This module consumes its `CurveVerification`, constructs the real curve certificate, and
applies the retained squarefree transfer.  The exceptional set precedes the challenge and candidate,
and the conclusion preserves the complete agreement set.

The ordinary-tail hypothesis is temporarily explicit.  It is the single seam filled by the shared
ordinary factor budget; the regular squarefree geometry and profile interpolation are discharged
here for every batching degree.
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ReedSolomon.CurveCertificate

open CurveProfile ReedSolomon.FirstOrder.Squarefree

noncomputable section

universe u

/-- The exact retained squarefree curve expression attached to a finite profile and split. -/
def squarefreeCurveEnvelope (p : LineProfile) (split : ℕ) : ℝ :=
  retainedSquarefreeCurveMCARaw
    (hybridTheta p.n p.D p.agreement) p.n p.D p.batchingDegree split
      p.agreement p.totalJetCap p.firstDerivativeCap p.height

/-- A verified finite curve profile inherits the retained squarefree semantic theorem.  The
interpolation degree stored in the certificate is `p.D`; recovery still uses the independently
specified code dimension `p.k`. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_of_tail
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split : ℕ) (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hcurve : 0 < p.batchingDegree + p.height)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F)
    (htail : ∀ cert : FirstOrderCurveCertificate.{u, u}
      p.D p.agreement p.multiplicity p.firstDerivativeCap p.totalJetCap
        p.k p.height domain
          (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
            p.columns,
      HasRetainedOrdinaryCurveTransfer
        (D := p.k - 1) (A := p.agreement) (B := p.totalJetCap)
        (M := p.firstDerivativeCap) (H := p.height) domain values iota
          (singularCurveEquation
            (extendSymbolicCoefficients iota cert.Q))) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ squarefreeCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  let curveWord : Fin p.n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hw : ∀ i, (curveWord i).natDegree ≤ p.batchingDegree := by
    intro i
    exact powerBatchedCoordinate_natDegree_le fun t ↦ values t i
  obtain ⟨cert⟩ := hp.exists_certificate domain curveWord hw
  have hresult :=
    exists_baseExceptional_retainedSquarefreeCurveMCA_of_certificate_of_tail
      domain values iota p.columns cert hk hsplit.1 hsplit.2.1 hsplit.2.2
        hcurve hM hMB hchar (htail cert)
  simpa only [squarefreeCurveEnvelope, LineProfile.D] using hresult

/-- A checked integer ceiling can be placed directly on the profile's semantic exceptional set. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_le_of_tail
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hcurve : 0 < p.batchingDegree + p.height)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (hbound : squarefreeCurveEnvelope p split ≤ budget)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F)
    (htail : ∀ cert : FirstOrderCurveCertificate.{u, u}
      p.D p.agreement p.multiplicity p.firstDerivativeCap p.totalJetCap
        p.k p.height domain
          (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
            p.columns,
      HasRetainedOrdinaryCurveTransfer
        (D := p.k - 1) (A := p.agreement) (B := p.totalJetCap)
        (M := p.firstDerivativeCap) (H := p.height) domain values iota
          (singularCurveEquation
            (extendSymbolicCoefficients iota cert.Q))) :
    ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ budget ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exact_powerAgreement_squarefree_of_tail
      hp split hsplit hk hcurve hM hMB domain values iota hchar htail
  exact ⟨exceptional, hcard.trans hbound, hgood⟩

end

end ReedSolomon.CurveCertificate
