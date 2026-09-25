/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Profile
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.SharpCurveMCA

/-!
# Sharp squarefree curve agreement from interpolation profiles

A curve-verified first-order interpolation profile supplies a finite curve certificate for every
received polynomial curve of its batching degree. The sharp retained squarefree charge then bounds
one base-field exceptional set, outside which every sufficiently agreeing candidate has exact
power agreement.

## Main statements

* `squarefreeSharpCurveEnvelope` is the sharp charge of a profile with the ordinary threshold
  at `D + 1`, and `squarefreeSharpOptimizedCurveEnvelope` minimizes that threshold.
* `squarefreeSharpOptimizedCurveEnvelope_le_fixed` compares the two envelopes.
* `exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized` bounds the exceptional set of
  a curve-verified profile by the optimized envelope.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial ReedSolomon.HiddenDerivative ReedSolomon.FirstOrder.Squarefree

namespace ReedSolomon

open ReedSolomon.HiddenDerivative.CurveProfile

noncomputable section

/-- The sharp retained squarefree charge of a profile at regular threshold `split`, with the
ordinary threshold fixed at `D + 1` for the candidate degree `D = k - 1`. -/
def squarefreeSharpCurveEnvelope (p : LineProfile) (split : ℕ) : ℚ :=
  retainedSquarefreeCurveSharpChargeAt p.n p.candidateDegree p.batchingDegree
    (p.candidateDegree + 1) split p.agreement p.totalJetCap p.firstDerivativeCap p.height

/-- The sharp retained squarefree charge of a profile at regular threshold `split`, with the
ordinary threshold minimized independently. -/
def squarefreeSharpOptimizedCurveEnvelope (p : LineProfile) (split : ℕ) : ℚ :=
  retainedSquarefreeCurveSharpOptimizedCharge p.n p.candidateDegree p.batchingDegree split
    p.agreement p.totalJetCap p.firstDerivativeCap p.height

/-- Minimizing the ordinary threshold is no worse than fixing it at `D + 1`. -/
theorem squarefreeSharpOptimizedCurveEnvelope_le_fixed (p : LineProfile) (split : ℕ)
    (hDA : p.candidateDegree < p.agreement) :
    squarefreeSharpOptimizedCurveEnvelope p split ≤ squarefreeSharpCurveEnvelope p split :=
  retainedSquarefreeCurveSharpOptimizedCharge_le_chargeAt (Nat.lt_succ_self _) hDA

universe u

/-- A curve-verified profile with `2 ≤ k`, positive batching degree, derivative cap
`1 ≤ M ≤ B` and regular threshold `k ≤ split ≤ A ≤ n` has, for every received curve over `F`,
one base-field exceptional set of size at most `squarefreeSharpOptimizedCurveEnvelope p split`.
Outside it, every candidate of degree `< k` with at least `A` agreements has exact power
agreement. `E` is an auxiliary algebraically closed field into which `iota` embeds `F`. -/
theorem exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification) (split : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap) (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F) (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max (p.k - 1) p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ squarefreeSharpOptimizedCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨cert⟩ := hp.exists_certificate domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i)
  exact exists_baseExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate
    domain values iota p.columns cert hk hsplit.1 hsplit.2.1 hsplit.2.2 hell hM hMB hchar

end

end ReedSolomon
