/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CertificateBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.RateGateCertificate

/-!
# Finite rate-gate list bound

The finite analytic inputs are isolated here before the general Gamma gate chooses
them. All ambient, field-characteristic, and integer agreement guards are derived
from the explicit block threshold.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative HiddenDerivative.RatePartition SimplexIntegration

open Classical in
/-- A finite partition moment and strict ratio bound the complete agreement list. -/
theorem close_list_bound_of_finite_rateGate {F : Type*} [Field F]
    {rate agreement : ℝ} {d m n k A : ℕ}
    (hrate : 0 < rate) (hgap : rate < agreement) (hagreement : agreement < 1)
    (hd : 0 < d) (hm : 0 < m)
    (hbudget : 0 < partitionWeightBudget rate agreement d m)
    (hgamma : 1 < finiteGamma rate agreement d m)
    (hn : rateBlockThreshold rate d m ≤ n) (hk : 0 < k) (hkRate : (k : ℝ) ≤ rate * n)
    (hA : agreement * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F)
    (hmoment : (27 / 10 : ℝ) < weightedSimplexExpectation d
      (partitionWeightBudget rate agreement d m)
      (fun point ↦ (max (Real.log (6 * (d : ℝ)) - (d : ℝ) * weightedRadius point /
        partitionWeightBudget rate agreement d m) 0) ^ 2)) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (rateJetCap rate m : ℝ) ^ 2 * (2 * rateJetCap rate m / (agreement - rate)) ^ d * n ^ d := by
  obtain ⟨horder, _, hkD, hDn, hjet, _, hnPos⟩ :=
    rateBlockThreshold_ambient hrate (hgap.trans hagreement) hn hkRate
  have hrealGap : (k : ℝ) + (agreement - rate) * n ≤ A := by nlinarith
  have hkA : k ≤ A := by
    apply (Nat.cast_le (α := ℝ)).mp
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  obtain ⟨certificate⟩ := SymbolicReceivedCurve.exists_rateGate_certificate_of_moment
    hrate (hgap.trans hagreement) (hrate.trans hgap) hd hm hbudget hgamma hn hkRate hA hAn
    domain (fun index ↦ Polynomial.C (received index)) (curveDegree := 0)
    (fun _ ↦ by simp) hmoment
  exact close_list_bound_of_curve_certificate domain received certificate hnPos hk
    (rateJetCap_pos hrate hm) hjet (by omega) (hkD.trans (Nat.le_succ _)) hDn hkA hAn
    (sub_pos.mpr hgap) hrealGap hchar

end ReedSolomon
