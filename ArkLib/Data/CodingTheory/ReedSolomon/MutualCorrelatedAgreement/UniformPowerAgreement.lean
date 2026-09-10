/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullAgreement
/-! # Uniform exact power-agreement contracts -/

@[expose] public section

noncomputable section
namespace ReedSolomon
open Polynomial

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- A scalar exceptional set works simultaneously for every degree-bounded candidate with
at least `L` agreements. This is the reusable leaf contract, including its quantifier order. -/
def UniformExactPowerAgreement {ℓ : ℕ} (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (k L E : ℕ) : Prop :=
  ∃ bad : Finset F, bad.card ≤ E ∧ ∀ z ∉ bad, ∀ Q : F[X], Q.degree < k →
    L ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
    HasExactPowerAgreement domain w (RingHom.id F) k z Q

/-- A group with one word uses no challenge and has no exceptional scalars. -/
theorem uniformExactPowerAgreement_singleton (domain : Fin n ↪ F)
    (w : Fin (0 + 1) → Fin n → F) (k L : ℕ) :
    UniformExactPowerAgreement domain w k L 0 := by
  refine ⟨∅, by simp, ?_⟩
  intro z _ Q hQ _
  refine ⟨fun _ ↦ Q, fun _ ↦ hQ, ?_, ?_⟩
  · simp [powerBatchedPolynomial]
  · ext i
    simp [polynomialAgreementSet, commonCurveAgreementSet, mappedDomain, powerBatchedWord]

end ReedSolomon
