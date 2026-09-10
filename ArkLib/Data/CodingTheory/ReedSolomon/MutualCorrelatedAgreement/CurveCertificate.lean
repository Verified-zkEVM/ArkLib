/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrderCurve
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator
/-!
# Mutual correlated agreement from finite interpolation profiles

A concrete application supplies a verified interpolation profile, a split threshold, and an
integer upper bound for the explicit geometric expression. This module turns those finite
checks into an actual exceptional set. The scalar-list companion lives in
`ListDecodability/FirstOrder/Profile.lean` and uses the same interpolation data.
It contains no system-specific parameter tables.

Read `exists_exceptional_exact_powerAgreement` from left to right: the domain and received
words are arbitrary; the interpolation and characteristic conditions are checked inputs. The
exceptional set is chosen before the challenge and candidate polynomial. Outside it, recovery
preserves the entire agreement set, not merely a subset of the required size. The algebraically
closed extension is used in the proof; the exceptional set and recovered polynomials lie in
the original field.
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ReedSolomon.CurveCertificate

open CurveProfile

noncomputable section

set_option maxRecDepth 4096

universe u

/-- Minimal common Taylor exponent used by the first-order geometry when `2 ≤ k`. -/
def taylorExponent (p : LineProfile) : ℕ := 2 * p.k - 3

/-- The chosen exponent is sufficient at every derivative order when `2 ≤ k`. -/
theorem taylorExponent_sufficient (p : LineProfile) (hk : 2 ≤ p.k) (r : ℕ) :
    TaylorExponentSufficient r p.k (taylorExponent p) := by
  simpa [taylorExponent] using taylorExponentSufficient_two_mul_sub_three r hk

/-- Evaluate the revised sharp expression at one profile and split.  Order-one stages use the
independent direct ratio from `k` to agreement `A`, while every stage uses `τ = 2k - 3`. -/
def envelope (p : LineProfile) (split : ℕ) : ℚ :=
  firstOrderCurveBound p.n p.k p.k split p.agreement p.totalJetCap
    p.firstDerivativeCap p.batchingDegree p.height (taylorExponent p)
      (firstOrderCurveDirectRatio p.n p.k p.agreement)

/-- Any verified concrete curve profile inherits the semantic exceptional-set theorem once a
split and integer ceiling have been checked. -/
theorem exists_exceptional_exact_powerAgreement
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hcurve : 0 < p.batchingDegree + p.height)
    (hbound : envelope p split ≤ budget)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.totalJetCap < ringChar F) :
    ∃ exceptional : Finset F, (exceptional.card : ℚ) ≤ budget ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  rcases hp with ⟨hD, hcoeff, hkD, hheight, _, _⟩
  have hk : 0 < p.k := by
    simp only [LineProfile.D] at hD
    omega
  have hK : 1 < p.k := by
    simp only [LineProfile.D] at hD
    omega
  have hheight' :
      firstOrderCurveShiftedRowSlotBound p.D p.agreement p.multiplicity
          p.firstDerivativeCap p.totalJetCap p.n p.batchingDegree p.height <
        firstOrderCurveShiftedHeightSlotCount p.D p.agreement p.multiplicity
          p.firstDerivativeCap p.totalJetCap p.batchingDegree p.height := by
    simpa only [LineProfile.shiftedRowSlots, LineProfile.shiftedHeightSlots] using hheight
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := p.D) (A := p.agreement) (m := p.multiplicity)
      (M := p.firstDerivativeCap) (mu := p.totalJetCap) (k := p.k)
      (h := p.height) (n := p.n) (K := p.k) (L := split)
      (ell := p.batchingDegree) domain values iota hD hcoeff hkD hheight'
        hK le_rfl hk hsplit.1 hsplit.2.1 hsplit.2.2 hcurve hchar
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  simpa only [envelope, taylorExponent] using hbound


end

end ReedSolomon.CurveCertificate
