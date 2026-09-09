/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Bounds
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds
/-!
# Rate-only slack bounds for actual first-order lists and MCA

The constants depend only on the physical rate. The automatic recipe proves their cubic list
and quintic exception envelopes, and the actual finite capstone supplies complete lists and
exact agreement sets. The final probability theorem specializes to uniform finite fields.
-/

namespace ReedSolomon
open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

open Classical in
/-- Complete lists and full agreement-set MCA with explicit constants depending only on rho. -/
theorem automaticFirstOrder_rate_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          automaticLambdaBoundConstant rho * n / eta ^ 3) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have ha : automaticFirstOrderThreshold rho < automaticFirstOrderThreshold rho + eta :=
    lt_add_of_pos_right _ heta
  obtain ⟨hlistBound, hexceptionBound⟩ := automaticHybridClosedBounds
    hrho hrhoOne heta haOne (by omega : 1 ≤ n) rfl hkRate hA
  obtain ⟨hlist, hmca⟩ := automaticFirstOrder_list_and_lineMCA rho
    (automaticFirstOrderThreshold rho + eta) n k A hrho hrhoOne ha haOne hn hk hkRate
    hA hAn domain hchar
  constructor
  · intro received
    obtain ⟨hf, hraw, hceil, hclosed⟩ := hlist received
    exact ⟨hf, hclosed.trans hlistBound⟩
  · intro f g
    obtain ⟨ex, hraw, hceil, hclosed, hgood⟩ := hmca f g
    exact ⟨ex, hclosed.trans hexceptionBound, hgood⟩

/-- Both rate-only constants are positive. -/
theorem automaticFirstOrder_rate_constants_pos (rho : ℝ) :
    0 < automaticLambdaBoundConstant rho ∧ 0 < automaticExceptionBoundConstant rho := by
  have hC : 0 < automaticHybridEnvelopeConstant rho :=
    lt_of_lt_of_le zero_lt_one (one_le_automaticHybridEnvelopeConstant rho)
  unfold automaticLambdaBoundConstant automaticExceptionBoundConstant
  constructor <;> positivity

open Classical in
/-- The quintic rate-only exceptional bound controls finite-field affine-line failure. -/
theorem automaticFirstOrder_rate_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (automaticFirstOrderThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5) /
          (Fintype.card F : ℝ))) := by
  let a := automaticFirstOrderThreshold rho + eta
  let A := Nat.ceil (a * n)
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  have hline : LineExactAgreementBound domain k A
      (automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5) := by
    intro f g
    obtain ⟨ex, hcard, hgood⟩ := (automaticFirstOrder_rate_bounds rho eta n k A
      hrho hrhoOne heta haOne hn hk hkRate hA hAn domain hchar).2 f g
    refine ⟨ex, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - (automaticFirstOrderThreshold rho + eta))) =
      a * n := by dsimp only [a]; ring
  rw [heq]
end ReedSolomon
