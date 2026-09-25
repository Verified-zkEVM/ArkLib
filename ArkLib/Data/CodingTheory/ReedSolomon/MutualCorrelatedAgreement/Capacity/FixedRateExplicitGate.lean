/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FixedRateGate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition

/-!
# Fixed-rate line agreement

The explicit fixed-rate order and its finite parameters give an exact correlated-agreement bound
uniformly over fields, code dimensions, evaluation domains, and received lines.

## Main statements

* `fixedRatePartitionOrder_line_exactCorrelatedPair`: exact agreement outside a bounded
  exceptional set at the explicit fixed-rate order.

## References

* [DKT26]
* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

open Classical in
/-- At positive rate `R` and gap `δ` with `R + δ < 1`, the explicit fixed-rate order gives an
exceptional-set bound for exact correlated agreement. One exceptional set of size at most
`C * n^(d+1)` works for every later challenge and close candidate, where `d` is the selected
order and `C` depends only on the selected finite parameters. Outside the set, the candidate is
a linear combination of degree-`< k` polynomials agreeing with the received words, and its full
agreement set equals their common agreement set. The field characteristic is zero or exceeds the
message, order, and jet-degree bounds.
-/
theorem fixedRatePartitionOrder_line_exactCorrelatedPair {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    -- Fix the explicit order and its finite interpolation parameters before the field and code.
    let p := RatePartition.fixedRatePartitionFiniteParameters hR hδ
    ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- The code is long enough, has rate at most `R`, and realizes agreement between `R + δ`
      -- and `1`.
      RatePartition.rateBlockThreshold R (RatePartition.fixedRatePartitionOrder R δ)
        p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      -- `domain` is injective; `f` and `g` determine the received line `f + z*g`.
      ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
      -- Characteristic zero or above the message, order, and selected jet-degree bounds.
      (ringChar F = 0 ∨
        max (max (k - 1) (RatePartition.fixedRatePartitionOrder R δ))
          (RatePartition.rateJetCap R p.multiplicity) < ringChar F) →
      -- Choose one exceptional set before either the challenge or candidate.
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ polynomialCurveProductAgreementConstant δ
          (RatePartition.rateJetCap R p.multiplicity)
          (RatePartition.marginHeight (RatePartition.rateJetCap R p.multiplicity)
            (RatePartition.partitionFiniteRatio R (R + δ)
              (RatePartition.fixedRatePartitionOrder R δ) p.multiplicity))
          (RatePartition.fixedRatePartitionOrder R δ) *
            (n : ℝ) ^ (RatePartition.fixedRatePartitionOrder R δ + 1) ∧
        -- The conclusion identifies the candidate's complete agreement set.
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  intro F _ n k A hn hk hkR haA hAn domain f g hchar
  simpa only [add_sub_cancel_left] using
    exists_ratePartition_line_exactCorrelatedPair
      (RatePartition.fixedRatePartitionFiniteParameters hR hδ) hR
      (by linarith : R < R + δ) haone
      (RatePartition.fixedRatePartitionOrder_ge_500 R δ)
      hn hk hkR haA hAn domain f g hchar

end ReedSolomon
