/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine

/-!
# Finite-field line MCA error for the automatic first-order recipe

Over a finite field, the automatic first-order recipe bounds the mutual correlated agreement
error of the affine-line generator for a Reed–Solomon code at radius `1 - a`. The agreement
threshold is rounded once as `⌈a n⌉₊`. Uniform challenge sampling turns each of the optimized,
ceiling, and closed exceptional-set bounds `E` into the error bound `min 1 (E / |F|)`.

## Main statements

* `ReedSolomon.automaticFirstOrder_hybrid_mcaError_le`: the three line MCA error bounds.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

/-- For a rate `rho` and an agreement fraction `a` above the first-order threshold, the MCA error
of the affine-line generator for the Reed–Solomon code of dimension `k` at radius `1 - a` is at
most `min 1 (E / |F|)`, where `E` is the optimized exception charge, its ceiling, or the closed
exception constant of the automatic recipe at the threshold `A = ⌈a n⌉₊`. -/
theorem automaticFirstOrder_hybrid_mcaError_le
    {rho a : ℝ} {n k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1) (automaticDerivativeCap rho a) < ringChar F) :
    let A := ⌈a * n⌉₊
    let θ := agreementIncidenceRatio n (k - 1) A
    let h := automaticChallengeHeight rho a
    let μ := automaticJetDegree rho a
    let M := automaticDerivativeCap rho a
    mcaError (AffineLineGenerator F) (code domain k) (1 - a) ≤
        min 1 (ENNReal.ofReal
          (maxMinFirstOrderExceptionCharge θ n (k - 1) A h μ M / Fintype.card F)) ∧
      mcaError (AffineLineGenerator F) (code domain k) (1 - a) ≤
        min 1 (ENNReal.ofReal
          ((firstOrderExceptionBound θ n (k - 1) A h μ M : ℝ) / Fintype.card F)) ∧
      mcaError (AffineLineGenerator F) (code domain k) (1 - a) ≤
        min 1 (ENNReal.ofReal
          (firstOrderExceptionConstant θ n (k - 1) h μ M / Fintype.card F)) := by
  classical
  dsimp only
  have hA : a * n ≤ (⌈a * n⌉₊ : ℝ) := Nat.le_ceil _
  have hAn : ⌈a * n⌉₊ ≤ n :=
    Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg n) haOne.le)
  have hthreshold : ⌈a * n⌉₊ ≤ ⌈(Fintype.card (Fin n) : ℝ) * (1 - (1 - a))⌉₊ := by
    rw [Fintype.card_fin, sub_sub_cancel, mul_comm]
  have hbase (f g : Fin n → F) := exists_automaticFirstOrder_hybridEquation_base
    hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn hchar domain f g
  refine ⟨mcaError_affineLine_le_min_one_of_exactAgreement domain _
      (lineExactAgreementBound_of_exactCorrelatedPair domain _ fun f g ↦ ?_) _ hthreshold,
    mcaError_affineLine_le_min_one_of_exactAgreement domain _
      (lineExactAgreementBound_of_exactCorrelatedPair domain _ fun f g ↦ ?_) _ hthreshold,
    mcaError_affineLine_le_min_one_of_exactAgreement domain _
      (lineExactAgreementBound_of_exactCorrelatedPair domain _ fun f g ↦ ?_) _ hthreshold⟩
  · obtain ⟨-, -, -, -, -, -, exceptional, hraw, -, -, hgood⟩ := hbase f g
    exact ⟨exceptional, hraw, hgood⟩
  · obtain ⟨-, -, -, -, -, -, exceptional, -, hceil, -, hgood⟩ := hbase f g
    exact ⟨exceptional, by exact_mod_cast hceil, hgood⟩
  · obtain ⟨-, -, -, -, -, -, exceptional, -, -, hclosed, hgood⟩ := hbase f g
    exact ⟨exceptional, hclosed, hgood⟩

end ReedSolomon
