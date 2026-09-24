/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FiniteSurplus
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateBound
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio

/-!
# Rate-dependent partition-support curve certificates

A strict finite-ratio surplus produces a symbolic received-curve certificate with challenge
height controlled by the ratio margin. The padded and mathematical block-length thresholds supply
the degree, dimension and agreement bounds needed for this construction.

## Main statements

* `exists_partitionSupport_curve_certificate_of_finiteRatio`: a finite-ratio surplus gives a
  certificate with height `ℓ * marginHeight ν γ`.
* `exists_partitionSupport_curve_certificate_of_paddedRateBlockThreshold` and
  `exists_partitionSupport_curve_certificate_of_rateBlockThreshold`: the two block-length
  thresholds supply the certificate parameters.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- A finite-ratio surplus gives a symbolic curve certificate whose challenge height is bounded
by `ℓ * marginHeight ν γ`. -/
theorem exists_partitionSupport_curve_certificate_of_finiteRatio {F : Type*} [Field F]
    {rate agreement γ : ℝ} {D d m n k A ℓ ν : ℕ}
    (hD : 0 < D) (hd : 500 ≤ d) (hm : 0 < m) (hrate : 0 < rate)
    (hagreement : 0 < agreement)
    (hbudget : 0 < RatePartition.partitionWeightBudget rate agreement d m)
    (hkD : k ≤ D + 1) (hupper : (D : ℝ) ≤ rate * n)
    (hagreementUpper : agreement * n ≤ A)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (hdegree : ∀ u, PartitionSupportEligible D d
      (RatePartition.partitionWeightBudget rate agreement d m) (m * A : ℕ) u →
        totalJetDegree u ≤ ν)
    (hγ : 1 < γ)
    (hγle : γ ≤ RatePartition.partitionFiniteRatio rate agreement d m) :
    Nonempty (SymbolicReceivedCurve.Certificate A k ℓ ν d
      (ℓ * RatePartition.marginHeight ν γ) centers received) := by
  let W := RatePartition.partitionWeightBudget rate agreement d m
  let r := n * localDerivativeCoordinateBudget d m W
  let N := (partitionSupportExponents D d W (m * A : ℕ) hD).card
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
    exact (not_le_of_gt hDreal) (by simpa using hupper)
  have hAreal : (0 : ℝ) < A :=
    (mul_pos hagreement (Nat.cast_pos.mpr hn)).trans_le hagreementUpper
  have hA : 0 < A := Nat.cast_pos.mp hAreal
  have hlevel : (m : ℝ) * agreement * n ≤ ((m * A : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hagreementUpper
      (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast at h ⊢
    nlinarith
  have hsurplus := partitionSupport_largeOrder_finiteRatio_surplus F hD hd hm
    hrate hagreement hbudget hupper hlevel
  have hdimension : RatePartition.partitionFiniteRatio rate agreement d m * (r : ℝ) < N := by
    simpa only [r, N, W, Nat.cast_mul, mul_assoc,
      finrank_partitionSupportSpace_eq_card] using hsurplus
  have hmargin : γ * (r : ℝ) < N :=
    (mul_le_mul_of_nonneg_right hγle (Nat.cast_nonneg r : (0 : ℝ) ≤ r)).trans_lt
      hdimension
  have hsurplusNat : r < N := by
    have hrN : (r : ℝ) < N := by
      nlinarith [Nat.cast_nonneg r (α := ℝ), Nat.cast_nonneg N (α := ℝ)]
    exact_mod_cast hrN
  have hsurplusNat' : n * localDerivativeCoordinateBudget d m W <
      (partitionSupportExponents D d W (m * A : ℕ) hD).card := by
    simpa only [r, N, W] using hsurplusNat
  obtain ⟨cert⟩ := exists_partitionSupport_curve_certificate (D := D) (d := d) (m := m)
    (W := W) (n := n) (A := A) (k := k) (ℓ := ℓ) (ν := ν)
    (L := ((m * A : ℕ) : ℝ))
    hD le_rfl (mul_pos hm hA) hkD centers received hreceived
    (by simpa only [W] using hdegree) hsurplusNat'
  have hheight := RatePartition.kernel_height_le_marginHeight (ℓ := ℓ) (ν := ν) hγ hmargin
  have hheight' : n * localDerivativeCoordinateBudget d m W * (ℓ * ν) /
      ((partitionSupportExponents D d W (m * A : ℕ) hD).card -
        n * localDerivativeCoordinateBudget d m W) ≤ ℓ * RatePartition.marginHeight ν γ := by
    simpa only [r, N, W] using hheight
  exact ⟨{ cert with challengeDegree_le := fun u ↦
    (cert.challengeDegree_le u).trans hheight' }⟩

/-- A padded rate block-length threshold gives a symbolic received-curve certificate using the
finite ratio of the selected multiplicity. -/
theorem exists_partitionSupport_curve_certificate_of_paddedRateBlockThreshold {F : Type*}
    [Field F] {rate agreement : ℝ} {d n k A ℓ : ℕ}
    (parameters : RatePartition.PartitionFiniteParameters rate agreement d)
    (hrate : 0 < rate) (hrateOne : rate < 1) (hagreement : 0 < agreement)
    (hd : 500 ≤ d)
    (hn : RatePartition.paddedRateBlockThreshold rate d parameters.multiplicity ≤ n)
    (hk : (k : ℝ) ≤ rate * n) (hagreementUpper : agreement * n ≤ A) (hAn : A ≤ n)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate A k ℓ (RatePartition.rateJetCap rate
      parameters.multiplicity) d
      (ℓ * RatePartition.marginHeight (RatePartition.rateJetCap rate parameters.multiplicity)
        (RatePartition.partitionFiniteRatio rate agreement d parameters.multiplicity))
      centers received) := by
  obtain ⟨hdD, hDlower, hkD, -, -, -, -, -⟩ :=
    RatePartition.paddedRateBlockThreshold_guards hrate hrateOne hn hk hagreementUpper
  have hD : 0 < ⌊rate * n⌋₊ := by omega
  have hDn : (⌊rate * n⌋₊ : ℝ) ≤ rate * n := Nat.floor_le (by positivity)
  have hdegree : ∀ u, PartitionSupportEligible (⌊rate * n⌋₊) d
      (RatePartition.partitionWeightBudget rate agreement d parameters.multiplicity)
      (parameters.multiplicity * A : ℕ) u →
      totalJetDegree u ≤ RatePartition.rateJetCap rate parameters.multiplicity := by
    intro u hu
    exact RatePartition.partitionSupport_totalJetDegree_le_rateJetCap
      (d := d) (W := RatePartition.partitionWeightBudget rate agreement d parameters.multiplicity)
      (m := parameters.multiplicity) (A := A) hD hrate hDlower hAn hu
  exact exists_partitionSupport_curve_certificate_of_finiteRatio hD hd
    parameters.multiplicity_pos hrate hagreement parameters.weightBudget_pos
    (hkD.trans (Nat.le_succ _)) hDn hagreementUpper centers received hreceived hdegree
    parameters.one_lt_finiteRatio le_rfl

/-- A mathematical rate block-length threshold gives a symbolic received-curve certificate using
the finite ratio of the selected multiplicity. -/
theorem exists_partitionSupport_curve_certificate_of_rateBlockThreshold {F : Type*} [Field F]
    {rate agreement : ℝ} {d n k A ℓ : ℕ}
    (parameters : RatePartition.PartitionFiniteParameters rate agreement d)
    (hrate : 0 < rate) (hrateOne : rate < 1) (hagreement : 0 < agreement)
    (hd : 500 ≤ d)
    (hn : RatePartition.rateBlockThreshold rate d parameters.multiplicity ≤ n)
    (hk : (k : ℝ) ≤ rate * n) (hagreementUpper : agreement * n ≤ A) (hAn : A ≤ n)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate A k ℓ (RatePartition.rateJetCap rate
      parameters.multiplicity) d
      (ℓ * RatePartition.marginHeight (RatePartition.rateJetCap rate parameters.multiplicity)
        (RatePartition.partitionFiniteRatio rate agreement d parameters.multiplicity))
      centers received) := by
  obtain ⟨hdD, hDlower, hkD, -, -, -, -, -⟩ :=
    RatePartition.rateBlockThreshold_guards hrate hrateOne hn hk hagreementUpper
  have hD : 0 < ⌊rate * n⌋₊ := by omega
  have hDn : (⌊rate * n⌋₊ : ℝ) ≤ rate * n := Nat.floor_le (by positivity)
  have hdegree : ∀ u, PartitionSupportEligible (⌊rate * n⌋₊) d
      (RatePartition.partitionWeightBudget rate agreement d parameters.multiplicity)
      (parameters.multiplicity * A : ℕ) u →
      totalJetDegree u ≤ RatePartition.rateJetCap rate parameters.multiplicity := by
    intro u hu
    exact RatePartition.partitionSupport_totalJetDegree_le_rateJetCap
      (d := d) (W := RatePartition.partitionWeightBudget rate agreement d parameters.multiplicity)
      (m := parameters.multiplicity) (A := A) hD hrate hDlower hAn hu
  exact exists_partitionSupport_curve_certificate_of_finiteRatio hD hd
    parameters.multiplicity_pos hrate hagreement parameters.weightBudget_pos
    (hkD.trans (Nat.le_succ _)) hDn hagreementUpper centers received hreceived hdegree
    parameters.one_lt_finiteRatio le_rfl

end ReedSolomon.HiddenDerivative
