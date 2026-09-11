/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp

/-!
# Optimized hybrid recovery from finite curve profiles

A curve-verified `LineProfile` directly supplies the literal shifted-height premise of the
optimized hybrid theorem.  The profile retains the squarefree theorem as an independent semantic
alternative.  Taking the smaller of their two proved bounds therefore gives another actual
recovery theorem, rather than merely a numerical comparison.

This is the semantic profile form of the optimized hybrid and factorwise-squarefree alternatives
in [DKTZ26, `lem:first-order-hybrid` and `lem:first-order-factorwise`]. The declarations return an
exceptional set and exact power agreement; they are not only envelope inequalities.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], first-order curve tuning.
-/

@[expose] public section

namespace ReedSolomon.CurveCertificate

open Polynomial ReedSolomon.HiddenDerivative
open ReedSolomon.CurveProfile

noncomputable section

set_option autoImplicit false

universe u

/-- The endpoint-aware optimized hybrid envelope attached to a finite profile. -/
def hybridOptimizedCurveEnvelope (p : LineProfile) : ℝ :=
  if p.D + 1 = p.n then 0 else
    hybridCurveOptimized p.n p.D p.batchingDegree p.agreement p.height
      p.totalJetCap p.firstDerivativeCap

/-- The better of the optimized hybrid and retained-squarefree semantic envelopes. -/
def bestCurveEnvelope (p : LineProfile) (split : ℕ) : ℝ :=
  min (hybridOptimizedCurveEnvelope p) (squarefreeSharpCurveEnvelope p split : ℝ)

theorem bestCurveEnvelope_le_hybrid (p : LineProfile) (split : ℕ) :
    bestCurveEnvelope p split ≤ hybridOptimizedCurveEnvelope p := by
  exact min_le_left _ _

theorem bestCurveEnvelope_le_squarefree (p : LineProfile) (split : ℕ) :
    bestCurveEnvelope p split ≤ (squarefreeSharpCurveEnvelope p split : ℝ) := by
  exact min_le_right _ _

open Classical in
/-- A curve-verified profile constructs optimized hybrid recovery with its literal profile
support, shifted height, and actual derivative cap. -/
theorem exists_exceptional_exact_powerAgreement_hybrid_optimized
    {F : Type u} [Field F]
    {p : LineProfile} (hp : p.CurveVerification)
    (hk : 2 ≤ p.k) (hA : p.k ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    (hell : 0 < p.batchingDegree)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (hchar : ringChar F = 0 ∨
      max p.D p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ hybridOptimizedCurveEnvelope p ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  have hDk : p.D + 1 = p.k := by
    simp only [LineProfile.D]
    omega
  have hD : 1 ≤ p.D := by omega
  have hDA : p.D < p.agreement := by omega
  have hheight :
      firstOrderCurveShiftedRowSlotBound p.D p.agreement p.multiplicity
          p.firstDerivativeCap p.totalJetCap p.n p.batchingDegree p.height <
        firstOrderCurveShiftedHeightSlotCount p.D p.agreement p.multiplicity
          p.firstDerivativeCap p.totalJetCap p.batchingDegree p.height := by
    simpa only [LineProfile.shiftedRowSlots, LineProfile.shiftedHeightSlots] using hp.2.2.2.1
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized_fullAgreement
      (D := p.D) (A := p.agreement) (m := p.multiplicity)
      (M := p.firstDerivativeCap) (mu := p.totalJetCap) (h := p.height)
      (ell := p.batchingDegree) domain values hD hp.2.1 hheight hell hDA hAn
        (Or.inr hchar)
  refine ⟨exceptional, ?_, ?_⟩
  · simpa only [hybridOptimizedCurveEnvelope] using hcard
  · intro z hz P hP hagreement
    have hP' : P.degree < p.D + 1 := by
      simpa only [← Nat.cast_add_one, hDk] using hP
    have hresult := hgood z hz P hP' hagreement
    simpa only [hDk] using hresult

open Classical in
/-- **Best certified first-order curve envelope with semantic recovery.**

The minimum of the independently proved optimized-hybrid and factorwise-squarefree envelopes still
has an actual recovery theorem. The chosen exceptional set comes from whichever theorem attains the
minimum, and every good challenge recovers exact power agreement with the complete agreement set. -/
theorem exists_exceptional_exact_powerAgreement_best
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max p.D p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ bestCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  by_cases hbest : hybridOptimizedCurveEnvelope p ≤
      (squarefreeSharpCurveEnvelope p split : ℝ)
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_exact_powerAgreement_hybrid_optimized hp hk
        (hsplit.1.trans hsplit.2.1) hsplit.2.2
        hell domain values hchar
    refine ⟨exceptional, ?_, hgood⟩
    simpa only [bestCurveEnvelope, min_eq_left hbest] using hcard
  · have hsquarefree : (squarefreeSharpCurveEnvelope p split : ℝ) ≤
        hybridOptimizedCurveEnvelope p := le_of_not_ge hbest
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_exact_powerAgreement_squarefree_sharp hp split hsplit hk hell hM hMB
        domain values iota hchar
    refine ⟨exceptional, ?_, hgood⟩
    have hcardReal : (exceptional.card : ℝ) ≤
        (squarefreeSharpCurveEnvelope p split : ℝ) := by
      exact_mod_cast hcard
    simpa only [bestCurveEnvelope, min_eq_right hsquarefree] using hcardReal

end

end ReedSolomon.CurveCertificate
