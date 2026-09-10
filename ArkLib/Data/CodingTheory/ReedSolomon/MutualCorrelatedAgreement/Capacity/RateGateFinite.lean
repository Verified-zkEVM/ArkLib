/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.CertificateBound
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.RateGateCertificate
/-!
# Exact finite rate-gate curve agreement

The actual variable-margin certificate chooses its exceptional set before the
challenge and candidate. The final conclusion is exact power agreement, with
the literal product-counting scalar and no replacement list-size assumption.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative HiddenDerivative.RatePartition SimplexIntegration
open Polynomial
open SymbolicReceivedInterpolation

universe u

/-- Finite rate-gate interpolation gives exact polynomial-curve mutual agreement. -/
theorem exists_curveMCA_of_finite_rateGate {F E : Type u} [Field F] [Field E]
    [DecidableEq E] [IsAlgClosed E] {rate agreement : ℝ} {d m n k A curveDegree : ℕ}
    (hrate : 0 < rate) (hgap : rate < agreement) (hagreement : agreement < 1)
    (hd : 0 < d) (hm : 0 < m) (hcurve : 0 < curveDegree)
    (hbudget : 0 < partitionWeightBudget rate agreement d m)
    (hgamma : 1 < finiteGamma rate agreement d m)
    (hn : rateBlockThreshold rate d m ≤ n) (hk : 0 < k) (hkRate : (k : ℝ) ≤ rate * n)
    (hA : agreement * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (values : Fin (curveDegree + 1) → Fin n → F) (embedding : F →+* E)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F)
    (hmoment : (27 / 10 : ℝ) < weightedSimplexExpectation d
      (partitionWeightBudget rate agreement d m)
      (fun point ↦ (max (Real.log (6 * (d : ℝ)) - (d : ℝ) * weightedRadius point /
        partitionWeightBudget rate agreement d m) 0) ^ 2)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (curveDegree : ℝ) *
        polynomialCurveProductMCAConstant (agreement - rate) (rateJetCap rate m)
          (rateHeight rate agreement d m) d * (n : ℝ) ^ (d + 1) ∧
      ∀ challenge ∉ exceptional, ∀ polynomial : E[X], polynomial.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain embedding)
          (powerBatchedWord (fun term index ↦ embedding (values term index)) challenge)
            polynomial).card →
        HasExactPowerAgreement domain values embedding k challenge polynomial := by
  obtain ⟨horder, _, hkD, hDn, hjet, _, hnPos⟩ :=
    rateBlockThreshold_ambient hrate (hgap.trans hagreement) hn hkRate
  have hrealGap : (k : ℝ) + (agreement - rate) * n ≤ A := by nlinarith
  have hkA : k ≤ A := by
    apply (Nat.cast_le (α := ℝ)).mp
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  obtain ⟨certificate⟩ := SymbolicReceivedCurve.exists_rateGate_certificate_of_moment
    hrate (hgap.trans hagreement) (hrate.trans hgap) hd hm hbudget hgamma hn hkRate hA hAn
    domain (fun index ↦ powerBatchedCoordinate fun term ↦ values term index)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _) hmoment
  have hheight : 0 < rateHeight rate agreement d m := lt_of_lt_of_le
    Nat.zero_lt_one (le_max_left 1 _)
  exact exists_curveMCA_of_certificate domain values embedding certificate
    (sub_pos.mpr hgap) (by linarith) hnPos hk hd (rateJetCap_pos hrate hm)
    hheight hcurve (by omega) (hkD.trans (Nat.le_succ _)) hDn hjet hkA hAn hrealGap le_rfl hchar

end ReedSolomon
