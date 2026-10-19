/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FixedRateGate

/-!
# Complete list bounds from the explicit fixed-rate gate

A positive rate and gap determine an explicit derivative order and a finite multiplicity. These
parameters give a complete Reed–Solomon list bound uniformly over fields, codes, evaluation
domains, and received words beyond a rate-dependent block-length threshold.

## Main statements

* `fixedRatePartitionOrder_list_bound_selected`: the list bound using the selected multiplicity.
* `fixedRatePartitionOrder_list_bound`: existence of parameters giving the same bound.

## References

* [DKT26]
* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- At positive rate `R` and gap `δ` with `R + δ < 1`, the selected multiplicity at the explicit
fixed-rate order gives a complete-list bound. For every field, sufficiently long code, admissible
agreement threshold, evaluation embedding, and received word, the full close-polynomial set is
finite and its cardinality is at most
`ν² * (2ν/δ)^d * n^d`, where `d` is the fixed-rate order and `ν` is the selected jet bound. -/
theorem fixedRatePartitionOrder_list_bound_selected {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    -- The interpolation parameters are fixed before the field and code.
    let p := RatePartition.fixedRatePartitionFiniteParameters hR hδ
    ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- The length threshold, rate, and agreement constraints are uniform in the code.
      RatePartition.rateBlockThreshold R (RatePartition.fixedRatePartitionOrder R δ)
        p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      -- Characteristic zero or a characteristic above the message, order, and jet caps.
      (ringChar F = 0 ∨ max (max (k - 1) (RatePartition.fixedRatePartitionOrder R δ))
        (RatePartition.rateJetCap R p.multiplicity) < ringChar F) →
      -- The complete agreement list is finite before its cardinality is bounded.
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (RatePartition.rateJetCap R p.multiplicity : ℝ) ^ 2 *
            (2 * RatePartition.rateJetCap R p.multiplicity / δ) ^
              RatePartition.fixedRatePartitionOrder R δ *
            n ^ RatePartition.fixedRatePartitionOrder R δ := by
  dsimp only
  intro F _ n k A hn hk hkR haA hAn domain received hchar
  simpa only [add_sub_cancel_left] using
    ratePartition_close_list_bound (RatePartition.fixedRatePartitionFiniteParameters hR hδ)
      hR (by linarith : R < R + δ) haone
      (RatePartition.fixedRatePartitionOrder_ge_500 R δ) hn hk hkR haA hAn domain received
      hchar

open Classical in
/-- At positive rate `R` and gap `δ` with `R + δ < 1`, some finite parameters at the explicit
fixed-rate order give a complete-list bound uniformly over fields and sufficiently long codes. -/
theorem fixedRatePartitionOrder_list_bound {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    ∃ p : RatePartition.PartitionFiniteParameters R (R + δ)
      (RatePartition.fixedRatePartitionOrder R δ),
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      RatePartition.rateBlockThreshold R (RatePartition.fixedRatePartitionOrder R δ)
        p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨ max (max (k - 1) (RatePartition.fixedRatePartitionOrder R δ))
        (RatePartition.rateJetCap R p.multiplicity) < ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (RatePartition.rateJetCap R p.multiplicity : ℝ) ^ 2 *
            (2 * RatePartition.rateJetCap R p.multiplicity / δ) ^
              RatePartition.fixedRatePartitionOrder R δ *
            n ^ RatePartition.fixedRatePartitionOrder R δ := by
  refine ⟨RatePartition.fixedRatePartitionFiniteParameters hR hδ, ?_⟩
  intro F _ n k A hn hk hkR haA hAn domain received hchar
  have hbound := fixedRatePartitionOrder_list_bound_selected hR hδ haone
  dsimp only at hbound
  exact hbound F n k A hn hk hkR haA hAn domain received hchar

end ReedSolomon
