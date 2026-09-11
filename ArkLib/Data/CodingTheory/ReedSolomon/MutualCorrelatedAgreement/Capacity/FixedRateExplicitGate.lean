/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FixedRateGate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition

/-! # Exact line MCA from the explicit fixed-rate factor-six gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

open Classical in
/-- At a fixed positive rate and gap, the explicit factor-six order and the least multiplicity
returned by the terminating search give one exceptional set for every close polynomial. -/
theorem fixedRatePartitionOrder_lineMCA {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    let p := fixedRatePartitionFiniteParameters hR hδ
    ∀ (F : Type u) [Field F] (n k A : ℕ),
      ratePartitionMathematicalLength R (fixedRatePartitionOrder R δ) p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
      (ringChar F = 0 ∨ max (max (k - 1) (fixedRatePartitionOrder R δ))
        (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant δ
          (ratePartitionJetBound R p.multiplicity)
          (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
            (ratePartitionFiniteRatio R (R + δ) (fixedRatePartitionOrder R δ)
              p.multiplicity))
          (fixedRatePartitionOrder R δ) * (n : ℝ) ^ (fixedRatePartitionOrder R δ + 1) ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  intro F _ n k A hn hk hkR haA hAn domain f g hchar
  simpa only [add_sub_cancel_left] using exists_ratePartition_lineMCA
    (fixedRatePartitionFiniteParameters hR hδ) hR (by linarith : R < R + δ) haone
      (fixedRatePartitionOrder_ge_500 R δ) hn hk hkR haA hAn domain f g hchar

end ReedSolomon
