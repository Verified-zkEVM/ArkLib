/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Profile
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.ListBound
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificates
/-!
# Finite first-order list bounds from interpolation profiles

A verified interpolation profile supplies the certificate and parameter data for finite-list
bounds. The tight envelope uses the exact derivative-capped list weight, while the squarefree
envelope includes the singular-degree contribution.

## Main statements

* `finiteListBound_of_profile` bounds every finite family satisfying the degree and agreement
  constraints by the tight profile envelope.
* `finiteSquarefreeListBound_of_profile` bounds every such family by the squarefree envelope.
* `tightListEnvelope` and `squarefreeListEnvelope` define these bounds from a line profile.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ReedSolomon

open ReedSolomon.HiddenDerivative.CurveProfile

noncomputable section

universe u

/-- The derivative-capped scalar-list bound associated with a first-order profile. -/
def tightListEnvelope (p : LineProfile) : ℚ :=
  firstOrderTightListWeight p.n p.agreement p.k p.k (2 * p.k - 3)
    p.totalJetCap p.firstDerivativeCap

/-- The squarefree list bound associated with a first-order profile. -/
def squarefreeListEnvelope (p : LineProfile) : ℝ :=
  (firstOrderCurveFiberStageOne p.k p.totalJetCap p.firstDerivativeCap
      (regularTaylorExponent (p.k - 1)) : ℝ) *
      ((p.n - p.k + 1 : ℕ) : ℝ) / (p.agreement - p.k + 1 : ℕ) +
    FirstOrder.Squarefree.ordinaryDegreeEnvelope p.totalJetCap p.firstDerivativeCap

/-- A curve-verified profile bounds every finite family of polynomials meeting its degree and
agreement constraints by the tight list envelope. -/
theorem finiteListBound_of_profile
    {p : LineProfile} (hp : p.CurveVerification)
    (hell : p.batchingDegree = 1)
    (hkA : p.k ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    {F : Type u} [Field F]
    (domain : Fin p.n ↪ F) (received : Fin p.n → F)
    (hchar : ringChar F = 0 ∨ max (p.k - 1) p.totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < p.k ∧
      p.agreement ≤ ({i : Fin p.n | P.eval (domain i) = received i} : Set (Fin p.n)).ncard) :
    (S.card : ℚ) ≤ tightListEnvelope p := by
  have hD := hp.1
  have hk : 0 < p.k := by
    simp only [LineProfile.candidateDegree] at hD
    omega
  have hK : 1 < p.k := by
    simp only [LineProfile.candidateDegree] at hD
    omega
  have hkD : p.k ≤ p.candidateDegree + 1 := by
    change p.k ≤ p.k - 1 + 1
    omega
  have hheight := hp.2.2.1
  rw [hell] at hheight
  obtain ⟨cert⟩ :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hp.1 hp.2.1 hkD domain received (fun _ ↦ 0) hheight
  simpa only [tightListEnvelope] using
    firstOrder_finite_agreement_solutions_card_le_tight domain received p.columns cert
      hK le_rfl hk hkA hAn hchar S hS

open Classical in
/-- A curve-verified profile bounds every finite family of polynomials meeting its degree and
agreement constraints by the squarefree list envelope. -/
theorem finiteSquarefreeListBound_of_profile
    {p : LineProfile} (hp : p.CurveVerification)
    (hell : p.batchingDegree = 1)
    (hkA : p.k ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    (hMμ : p.firstDerivativeCap ≤ p.totalJetCap)
    {F : Type u} [Field F]
    (domain : Fin p.n ↪ F) (received : Fin p.n → F)
    (hchar : ringChar F = 0 ∨ max (p.k - 1) p.firstDerivativeCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < p.k ∧
      p.agreement ≤ ({i : Fin p.n | P.eval (domain i) = received i} : Set (Fin p.n)).ncard) :
    (S.card : ℝ) ≤ squarefreeListEnvelope p := by
  have hD := hp.1
  have hk : 2 ≤ p.k := by
    simp only [LineProfile.candidateDegree] at hD
    omega
  have hkD : p.k ≤ p.candidateDegree + 1 := by
    change p.k ≤ p.k - 1 + 1
    omega
  have hheight := hp.2.2.1
  rw [hell] at hheight
  obtain ⟨cert⟩ :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hp.1 hp.2.1 hkD domain received (fun _ ↦ 0) hheight
  have hS' : ∀ P ∈ S, P.degree < p.k ∧
      p.agreement ≤ (Finset.univ.filter fun i ↦
        P.eval (domain i) = received i).card := by
    intro P hP
    refine ⟨(hS P hP).1, ?_⟩
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    have hagreement :
        ({i : Fin p.n | P.eval (domain i) = received i} : Set (Fin p.n)) =
          (indices : Set (Fin p.n)) := by
      ext i
      simp [indices]
    have hcount := (hS P hP).2
    rw [hagreement, Set.ncard_coe_finset] at hcount
    exact hcount
  simpa only [squarefreeListEnvelope] using
    FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
      domain received p.columns cert hk hkA hAn hMμ hchar S hS'

end

end ReedSolomon
