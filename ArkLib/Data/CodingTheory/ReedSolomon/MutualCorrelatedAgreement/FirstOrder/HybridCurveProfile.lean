/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveRecovery
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Profile

/-!
# Best first-order curve envelopes

A verified interpolation profile gives both optimized hybrid recovery and sharp squarefree
recovery. The smaller of their exceptional-set bounds still has a recovery theorem: whichever
bound is smaller supplies one exceptional set fixed before every challenge and candidate.
The squarefree ordinary threshold may either be fixed at the candidate degree plus one or
minimized independently of the regular threshold. The two alternatives correspond to
[DKTZ26, `lem:first-order-hybrid` and `lem:first-order-factorwise`].

## Main statements

* `hybridOptimizedCurveEnvelope` is the hybrid bound, including the full-dimension endpoint.
* `bestCurveEnvelope` and `bestOptimizedCurveEnvelope` take the smaller certified bound.
* `exists_exceptional_exactPowerAgreement_hybridOptimized` specializes hybrid curve recovery
  to a verified profile.
* `exists_exceptional_exactPowerAgreement_bestOptimized` gives semantic recovery at the
  independently optimized best bound.

## References

* [DKTZ26]
-/

@[expose] public section

open Polynomial ReedSolomon.HiddenDerivative

namespace ReedSolomon

open ReedSolomon.HiddenDerivative.CurveProfile

noncomputable section

/-- The optimized hybrid curve bound of a profile, zero at full message dimension. -/
def hybridOptimizedCurveEnvelope (p : LineProfile) : ℝ :=
  if p.candidateDegree + 1 = p.n then 0 else
    hybridCurveOptimized p.n p.candidateDegree p.batchingDegree p.agreement p.height
      p.totalJetCap p.firstDerivativeCap

/-- The smaller of the optimized hybrid and fixed-threshold squarefree curve bounds. -/
def bestCurveEnvelope (p : LineProfile) (split : ℕ) : ℝ :=
  min (hybridOptimizedCurveEnvelope p) (squarefreeSharpCurveEnvelope p split)

/-- The smaller of the optimized hybrid and independently optimized squarefree curve bounds. -/
def bestOptimizedCurveEnvelope (p : LineProfile) (split : ℕ) : ℝ :=
  min (hybridOptimizedCurveEnvelope p) (squarefreeSharpOptimizedCurveEnvelope p split)

/-- Optimizing the squarefree ordinary threshold can only lower the best curve bound. -/
theorem bestOptimizedCurveEnvelope_le_best (p : LineProfile) (split : ℕ)
    (hDA : p.candidateDegree < p.agreement) :
    bestOptimizedCurveEnvelope p split ≤ bestCurveEnvelope p split := by
  exact min_le_min le_rfl (squarefreeSharpOptimizedCurveEnvelope_le_fixed p split hDA)

/-- The best fixed-threshold curve bound is no larger than its hybrid branch. -/
theorem bestCurveEnvelope_le_hybrid (p : LineProfile) (split : ℕ) :
    bestCurveEnvelope p split ≤ hybridOptimizedCurveEnvelope p := min_le_left _ _

/-- The best fixed-threshold curve bound is no larger than its squarefree branch. -/
theorem bestCurveEnvelope_le_squarefree (p : LineProfile) (split : ℕ) :
    bestCurveEnvelope p split ≤ squarefreeSharpCurveEnvelope p split := min_le_right _ _

universe u

open Classical in
/-- A verified profile gives one exceptional set at the optimized hybrid bound. Outside it,
every sufficiently agreeing candidate of degree below `k` has exact power agreement. -/
theorem exists_exceptional_exactPowerAgreement_hybridOptimized
    {F : Type u} [Field F]
    {p : LineProfile} (hp : p.CurveVerification)
    (hkA : p.k ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    (hell : 0 < p.batchingDegree)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (hchar : ringChar F = 0 ∨
      max p.candidateDegree p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ hybridOptimizedCurveEnvelope p ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  have hD : 1 ≤ p.candidateDegree := hp.1
  have hDk : p.candidateDegree + 1 = p.k := by
    simp only [LineProfile.candidateDegree] at hD ⊢
    omega
  have hDA : p.candidateDegree < p.agreement :=
    (by omega : p.candidateDegree < p.k).trans_le hkA
  have hheight :
      firstOrderCurveShiftedRowSlotBound p.candidateDegree p.agreement p.multiplicity
          p.firstDerivativeCap p.totalJetCap p.n p.batchingDegree p.height <
        firstOrderCurveShiftedHeightSlotCount p.candidateDegree p.agreement p.multiplicity
          p.firstDerivativeCap p.totalJetCap p.batchingDegree p.height := by
    simpa only [LineProfile.shiftedRowSlots, LineProfile.shiftedHeightSlots] using hp.2.2.1
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized
      (D := p.candidateDegree) (A := p.agreement) (m := p.multiplicity)
      (M := p.firstDerivativeCap) (mu := p.totalJetCap) (h := p.height)
      (ell := p.batchingDegree) domain values hD hp.2.1 hheight hell hDA hAn
      (Or.inr hchar)
  refine ⟨exceptional, ?_, ?_⟩
  · simpa only [hybridOptimizedCurveEnvelope] using hcard
  · intro z hz P hP hagreement
    have hP' : P.degree < p.candidateDegree + 1 := by
      simpa only [← Nat.cast_add_one, hDk] using hP
    simpa only [hDk] using hgood z hz P hP' hagreement

open Classical in
/-- A verified profile gives one exceptional set at the independently optimized best bound.
Every sufficiently agreeing low-degree candidate outside the set has exact power agreement. -/
theorem exists_exceptional_exactPowerAgreement_bestOptimized
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification) (split : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max p.candidateDegree p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ bestOptimizedCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  by_cases hbest : hybridOptimizedCurveEnvelope p ≤
      squarefreeSharpOptimizedCurveEnvelope p split
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_exactPowerAgreement_hybridOptimized hp
        (hsplit.1.trans hsplit.2.1) hsplit.2.2 hell domain values hchar
    refine ⟨exceptional, ?_, hgood⟩
    simpa only [bestOptimizedCurveEnvelope, min_eq_left hbest] using hcard
  · have hsquarefree : squarefreeSharpOptimizedCurveEnvelope p split ≤
        hybridOptimizedCurveEnvelope p := le_of_not_ge hbest
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized hp split hsplit
        hell hM hMB domain values iota hchar
    refine ⟨exceptional, ?_, hgood⟩
    simpa only [bestOptimizedCurveEnvelope, min_eq_right hsquarefree] using hcard

open Classical in
/-- A verified profile gives semantic recovery at the best bound with fixed squarefree
ordinary threshold. -/
theorem exists_exceptional_exactPowerAgreement_best
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification) (split : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max p.candidateDegree p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ bestCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_bestOptimized hp split hsplit hell hM hMB
      domain values iota hchar
  have hDA : p.candidateDegree < p.agreement := by
    have hD : 0 < p.candidateDegree := hp.1
    simp only [LineProfile.candidateDegree] at hD ⊢
    omega
  exact ⟨exceptional, hcard.trans (bestOptimizedCurveEnvelope_le_best p split hDA), hgood⟩

end

end ReedSolomon
