/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Asymptotics

/-! # The fixed-rate list exponent `R*log(40/(9R))` -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- Every positive exponent slack works for all sufficiently small positive agreement gaps. -/
theorem fixedRate_list_bound {R ε : ℝ}
    (hR : 0 < R) (hRone : R < 1) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      let d := ⌈Real.exp ((ratePartitionExponent R + ε) / δ)⌉₊
      ∃ p : RatePartitionFiniteParameters R (R + δ) d,
        ∀ (F : Type u) [Field F] (n k A : ℕ),
        ratePartitionMathematicalLength R d p.multiplicity ≤ n → 0 < k →
        (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
        ∀ (domain : Fin n ↪ F) (received : Fin n → F),
        (ringChar F = 0 ∨
          max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) →
        (closePolynomialSet domain received k A).Finite ∧
          ((closePolynomialSet domain received k A).ncard : ℝ) ≤
            (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
              (2 * ratePartitionJetBound R p.multiplicity / δ) ^ d * n ^ d := by
  obtain ⟨δ₀, hδ₀, hgate⟩ := ratePartition_fixedRate_eventually hR hRone hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hsmall
  obtain ⟨ha, hd, hg⟩ := hgate δ hδ hsmall
  simpa only [add_sub_cancel_left] using
    exists_ratePartition_list_bound hR (by linarith : R < R + δ) ha hd hg

end ReedSolomon
