/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Asymptotics
/-! # The fixed-rate exact line-MCA exponent -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

open Classical in
/-- Positive slack above the fixed-rate exponent gives exact line MCA
at sufficiently small gaps. -/
theorem fixedRate_lineMCA {R ε : ℝ}
    (hR : 0 < R) (hRone : R < 1) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      let d := ⌈Real.exp ((ratePartitionExponent R + ε) / δ)⌉₊
      ∃ p : RatePartitionFiniteParameters R (R + δ) d,
        ∀ (F : Type u) [Field F] (n k A : ℕ),
        ratePartitionMathematicalLength R d p.multiplicity ≤ n → 0 < k →
        (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
        ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
        (ringChar F = 0 ∨
          max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) →
        ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant δ
            (ratePartitionJetBound R p.multiplicity)
            (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
              (ratePartitionFiniteRatio R (R + δ) d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨δ₀, hδ₀, hgate⟩ := ratePartition_fixedRate_eventually hR hRone hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hsmall
  obtain ⟨ha, hd, hg⟩ := hgate δ hδ hsmall
  simpa only [add_sub_cancel_left] using
    exists_ratePartition_lineMCA_parameters hR (by linarith : R < R + δ) ha hd hg

end ReedSolomon
