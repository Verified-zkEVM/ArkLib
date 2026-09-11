/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CertificateList
/-!
# Finite list bounds from first-order interpolation profiles

A verified profile supplies the scalar differential equation. The derivative-capped
list theorem then bounds every finite family of qualifying candidates. This interface
uses the shared profile without importing mutual correlated agreement.
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ReedSolomon.CurveCertificate

open CurveProfile

noncomputable section

universe u

/-- The derivative-degree scalar-list expression attached to a finite profile. -/
def tightListEnvelope (p : LineProfile) : ℚ :=
  firstOrderTightListWeight p.n p.agreement p.k p.k (2 * p.k - 3)
    p.totalJetCap p.firstDerivativeCap

/-- The reduced-product/resultant list envelope attached to a finite profile. -/
def squarefreeListEnvelope (p : LineProfile) : ℝ :=
  (firstOrderCurveFiberStageOne p.k p.totalJetCap p.firstDerivativeCap
      (2 * p.k - 3) : ℝ) *
      ((p.n - p.k + 1 : ℕ) : ℝ) / (p.agreement - p.k + 1 : ℕ) +
    FirstOrder.Squarefree.ordinaryDegreeEnvelope p.totalJetCap p.firstDerivativeCap

/-- A verified curve profile also constructs the scalar equation used by the tight finite
list theorem, including the endpoint `D = 1`. -/
theorem finiteListBound_of_profile
    {p : LineProfile} (hp : p.CurveVerification)
    (hell : p.batchingDegree = 1) (hkn : p.k ≤ p.n)
    (hkA : p.k ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    {F : Type u} [Field F]
    (domain : Fin p.n ↪ F) (received : Fin p.n → F)
    (hchar : ringChar F = 0 ∨ max (p.k - 1) p.totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received p.k p.agreement P) :
    (S.card : ℚ) ≤ tightListEnvelope p := by
  have hD := hp.1
  have hk : 0 < p.k := by
    simp only [LineProfile.D] at hD
    omega
  have hK : 1 < p.k := by
    simp only [LineProfile.D] at hD
    omega
  have hheight := hp.2.2.2.1
  rw [hell] at hheight
  obtain ⟨cert⟩ :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hp.1 hp.2.1 hp.2.2.1 domain received (fun _ ↦ 0) hheight
  simpa only [tightListEnvelope] using
    firstOrder_finite_agreement_solutions_card_le_tight domain received p.columns cert
      hK le_rfl hkn hk hkA hAn hchar S hS

/-- A verified positive-first-derivative profile feeds directly into the squarefree
product/resultant count.  The characteristic guard depends on the derivative cap, and the
agreement conclusion concerns every member of the supplied finite family. -/
theorem finiteSquarefreeListBound_of_profile
    {p : LineProfile} (hp : p.CurveVerification)
    (hell : p.batchingDegree = 1) (hkn : p.k ≤ p.n)
    (hkA : p.k ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    (hM : 0 < p.firstDerivativeCap)
    (hMμ : p.firstDerivativeCap ≤ p.totalJetCap)
    {F : Type u} [Field F]
    (domain : Fin p.n ↪ F) (received : Fin p.n → F)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received p.k p.agreement P) :
    (S.card : ℝ) ≤ squarefreeListEnvelope p := by
  have hD := hp.1
  have hk : 2 ≤ p.k := by
    simp only [LineProfile.D] at hD
    omega
  have hheight := hp.2.2.2.1
  rw [hell] at hheight
  obtain ⟨cert⟩ :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hp.1 hp.2.1 hp.2.2.1 domain received (fun _ ↦ 0) hheight
  simpa only [squarefreeListEnvelope] using
    FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
      domain received p.columns cert hk hkn hkA hAn hM hMμ hchar S hS


end

end ReedSolomon.CurveCertificate
