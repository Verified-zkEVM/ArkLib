/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.RatePartition
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Gate

/-!
# Fixed-rate capacity at the exact exponential derivative order

Every positive epsilon in the exponent supplies an eventual gap range. Within that range,
one actual finite partition choice gives both complete lists and full agreement-set MCA.
The block-length requirement and the stronger general-order characteristic guard are explicit.
-/

namespace ReedSolomon
open Polynomial HiddenDerivative
universe u

open Classical in
/-- The scalar fixed-rate gate drives both mathematical capacity conclusions using the same
finite parameters, chosen before the field, block length, and received words. -/
theorem exists_fixedRate_capacity_bounds {R epsilon : ℝ}
    (hR : 0 < R) (hRone : R < 1) (hepsilon : 0 < epsilon) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ ∀ delta : ℝ, 0 < delta → delta < deltaZero →
      let d := Nat.ceil (Real.exp ((RatePartition.fixedRateCoefficient R + epsilon) / delta))
      ∃ p : RatePartitionFiniteParameters R (R + delta) d,
        ∀ (F : Type u) [Field F] (n k A : ℕ),
        ratePartitionLength R d p.multiplicity ≤ n → 0 < k →
        (k : ℝ) ≤ R * n → (R + delta) * n ≤ A → A ≤ n →
        ∀ (domain : Fin n ↪ F),
        (ringChar F = 0 ∨ n ≤ ringChar F) →
        (∀ received : Fin n → F,
          (closePolynomialSet domain received k A).Finite ∧
            ((closePolynomialSet domain received k A).ncard : ℝ) ≤
              (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
                (2 * ratePartitionJetBound R p.multiplicity / delta) ^ d * n ^ d) ∧
        ∀ f g : Fin n → F, ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant delta
            (ratePartitionJetBound R p.multiplicity)
            (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
              (ratePartitionFiniteRatio R (R + delta) d p.multiplicity)) d *
              (n : ℝ) ^ (d + 1) ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨deltaZero, hzero, hsmall⟩ :=
    RatePartition.exists_small_gap_rate_gate hR hRone hepsilon
  refine ⟨deltaZero, hzero, ?_⟩
  intro delta hdelta hdeltaZero
  dsimp only
  let d := Nat.ceil (Real.exp ((RatePartition.fixedRateCoefficient R + epsilon) / delta))
  obtain ⟨haone, hd, hgate⟩ := hsmall delta hdelta hdeltaZero
  have hRa : R < R + delta := lt_add_of_pos_right R hdelta
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa)
    (show 0 < d by dsimp [d]; omega) hgate
  refine ⟨p, ?_⟩
  intro F instF n k A hn hk hkR haA hAn domain hchar
  constructor
  · intro received
    simpa only [add_sub_cancel_left] using
      ratePartition_close_list_bound p hR hRa haone hd hn hk hkR haA hAn
        domain received hchar
  · intro f g
    simpa only [add_sub_cancel_left] using
      exists_ratePartition_lineMCA p hR hRa haone hd hn hk hkR haA hAn domain f g hchar
end ReedSolomon
