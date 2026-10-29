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
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformEnvelope

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
* `RatePartitionEnvelope.exists_curve_certificate`: a closed-form multiplicity envelope gives a
  uniform jet cap and challenge height `150ν`.

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

private theorem exists_partitionSupport_curve_certificate_of_rateBlockGuards {F : Type*}
    [Field F] {rate agreement : ℝ} {d n k A ℓ : ℕ}
    (parameters : RatePartition.PartitionFiniteParameters rate agreement d)
    (hrate : 0 < rate) (hagreement : 0 < agreement) (hd : 500 ≤ d)
    (hD : 0 < ⌊rate * n⌋₊)
    (hDlower : rate * n / 2 ≤ ⌊rate * n⌋₊)
    (hkD : k ≤ ⌊rate * n⌋₊)
    (hagreementUpper : agreement * n ≤ A) (hAn : A ≤ n)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate A k ℓ (RatePartition.rateJetCap rate
      parameters.multiplicity) d
      (ℓ * RatePartition.marginHeight (RatePartition.rateJetCap rate parameters.multiplicity)
        (RatePartition.partitionFiniteRatio rate agreement d parameters.multiplicity))
      centers received) := by
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
  exact exists_partitionSupport_curve_certificate_of_rateBlockGuards parameters hrate hagreement
    hd hD hDlower hkD hagreementUpper hAn centers received hreceived

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
  exact exists_partitionSupport_curve_certificate_of_rateBlockGuards parameters hrate hagreement
    hd hD hDlower hkD hagreementUpper hAn centers received hreceived

namespace RatePartition

/-- A closed-form multiplicity envelope gives a symbolic curve certificate with total-jet cap
`⌈m / δ²⌉₊ - 1` and challenge height `150` times that cap. -/
theorem RatePartitionEnvelope.exists_curve_certificate {F : Type*} [Field F]
    {δ scale : ℝ} {n k A ℓ : ℕ}
    (e : RatePartitionEnvelope δ (closedMultiplicity scale (uniformDerivativeOrder δ)) n k A)
    (hδ : 0 < δ) (hδone : δ < 1) (hd : 500 ≤ uniformDerivativeOrder δ)
    (hscale : 1 < scale * (uniformDerivativeOrder δ : ℝ) ^ 3)
    (hAn : A ≤ n) (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate A k ℓ
      (⌈(closedMultiplicity scale (uniformDerivativeOrder δ) : ℝ) / δ ^ 2⌉₊ - 1)
      (uniformDerivativeOrder δ)
      (ℓ * (150 * (⌈(closedMultiplicity scale (uniformDerivativeOrder δ) : ℝ) /
        δ ^ 2⌉₊ - 1))) centers received) := by
  let d := uniformDerivativeOrder δ
  let m := closedMultiplicity scale d
  let ν := ⌈(m : ℝ) / δ ^ 2⌉₊ - 1
  have hdpos : 0 < d := by dsimp [d]; exact uniformDerivativeOrder_pos δ
  have hmpos : 0 < m := by
    apply Nat.ceil_pos.mpr
    have hscale_pos : 0 < scale := by
      by_contra h
      have hscale_nonpos : scale ≤ 0 := le_of_not_gt h
      have hd3_nonneg : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
      nlinarith
    have hdcast : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hlog : 0 < Real.log (6 * (d : ℝ)) := Real.log_pos (by nlinarith)
    exact mul_pos (mul_pos hscale_pos (by positivity)) hlog
  have hνpos : 0 < ν := by
    have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hδ2one : δ ^ 2 < 1 := by nlinarith [hδone]
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hratio : 1 < (m : ℝ) / δ ^ 2 := (lt_div_iff₀ hδ2).2 (by linarith)
    have hratio' : (↑(1 : ℕ) : ℝ) < (m : ℝ) / δ ^ 2 := by simpa using hratio
    have hceil : 1 < ⌈(m : ℝ) / δ ^ 2⌉₊ := Nat.lt_ceil.mpr hratio'
    dsimp [ν]
    omega
  have hD : 0 < e.ambientDegree := by
    have horder := e.order_le
    omega
  have hW : 0 < partitionWeightBudget e.rate e.agreement d m := by
    simpa only [d, m] using partitionWeightBudget_closedMultiplicity_pos
      e.rate_pos e.rate_lt_agreement.le hscale
  have hdegree : ∀ u, PartitionSupportEligible e.ambientDegree d
      (partitionWeightBudget e.rate e.agreement d m) (m * A : ℕ) u →
      totalJetDegree u ≤ ν := by
    intro u hu
    exact partitionSupport_totalJetDegree_le_of_ambient_lower_bound hD hδ
      e.ambient_lower hAn hu
  obtain ⟨cert⟩ := exists_partitionSupport_curve_certificate_of_finiteRatio hD hd
    hmpos e.rate_pos (e.rate_pos.trans e.rate_lt_agreement) hW e.message_le
    e.rate_upper e.agreement_lower centers received hreceived hdegree
    (by norm_num : (1 : ℝ) < 151 / 150) e.ratio_gt.le
  have hγeq : (151 / 150 : ℝ) = 1 + 1 / (150 : ℝ) := by norm_num
  have hheight : marginHeight ν (151 / 150 : ℝ) = 150 * ν := by
    rw [hγeq]
    exact marginHeight_one_add_inv hνpos (by norm_num)
  have cert' : Nonempty (SymbolicReceivedCurve.Certificate A k ℓ ν d
      (ℓ * (150 * ν)) centers received) := by
    simpa only [hheight] using (show Nonempty _ from ⟨cert⟩)
  simpa only [d, m, ν] using cert'

end RatePartition

end ReedSolomon.HiddenDerivative
