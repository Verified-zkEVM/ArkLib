/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FixedRateGate

/-! # Complete list bound from the explicit fixed-rate factor-six gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The explicit factor-six order together with the least multiplicity returned by the
terminating search bounds every complete close-polynomial list. -/
theorem fixedRatePartitionOrder_list_bound_selected {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    let p := fixedRatePartitionFiniteParameters hR hδ
    ∀ (F : Type u) [Field F] (n k A : ℕ),
      ratePartitionMathematicalLength R (fixedRatePartitionOrder R δ) p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨ max (max (k - 1) (fixedRatePartitionOrder R δ))
        (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / δ) ^
              fixedRatePartitionOrder R δ *
            n ^ fixedRatePartitionOrder R δ := by
  dsimp only
  intro F _ n k A hn hk hkR haA hAn domain received hchar
  simpa only [add_sub_cancel_left] using ratePartition_close_list_bound
    (fixedRatePartitionFiniteParameters hR hδ) hR (by linarith : R < R + δ) haone
      (fixedRatePartitionOrder_ge_500 R δ) hn hk hkR haA hAn domain received hchar

open Classical in
/-- At a fixed positive rate and margin, the explicit factor-six derivative order admits a
terminating search for the finite interpolation multiplicity and hence bounds every complete
close-polynomial list.  No 300-based closed multiplicity is asserted at this minimal cutoff. -/
theorem fixedRatePartitionOrder_list_bound {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    ∃ p : RatePartitionFiniteParameters R (R + δ) (fixedRatePartitionOrder R δ),
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      ratePartitionMathematicalLength R (fixedRatePartitionOrder R δ) p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨ max (max (k - 1) (fixedRatePartitionOrder R δ))
        (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / δ) ^
              fixedRatePartitionOrder R δ *
            n ^ fixedRatePartitionOrder R δ := by
  exact ⟨fixedRatePartitionFiniteParameters hR hδ,
    fixedRatePartitionOrder_list_bound_selected hR hδ haone⟩

end ReedSolomon
