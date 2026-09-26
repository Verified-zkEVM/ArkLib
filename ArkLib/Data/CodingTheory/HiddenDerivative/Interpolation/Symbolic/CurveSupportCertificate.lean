/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Soundness
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold

/-!
# Weighted-support certificates for polynomial curves

Weighted-support interpolation constructs symbolic certificates for polynomial curves. A strict
dimension margin gives a certificate with bounded challenge degree and total jet degree; prescribed
rate and block parameters provide this margin.

## Main statements

* `exists_certificate_of_fixed_margin`: a dimension margin constructs a curve certificate.
* `exists_weightedSupport_certificate_of_rate` and `exists_prescribed_certificate`: rate and block
  parameters construct curve certificates.

## References

* [DKTZ26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.WeightedSupportParameters
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
open scoped BigOperators

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

/-- A strict weighted-support margin constructs a certificate for a polynomial curve. -/
theorem exists_certificate_of_fixed_margin {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    {d D m W A k ℓ : ℕ} {g₀ : ℝ} (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m)
    (hℓ : 0 < ℓ) (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ))
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1) (centers : ι ↪ F) (w : ι → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hmargin : (543 / 500 : ℝ) * Fintype.card ι * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (Certificate A k ℓ (2 * m - 1) d (12 * (ℓ * (2 * m - 1)) - 1) centers w) := by
  let ν := 2 * m - 1
  let L := (D : ℝ) * m * (1 + g₀)
  let columns := weightedSupportColumns (d := d) (W := W) (L := L) hD
  let N := Fintype.card (weightedSupportExponents D d W L hD)
  let r := Fintype.card ι * Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0))
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hcut : L ≤ (D : ℝ) * ((2 * m : ℕ) : ℝ) := by
    dsimp only [L]
    exact weightedSupportCutoff_le_two_mul D m hg₁
  have hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent := by
    intro j
    simpa only [columns] using
      (weightedSupportColumns_eligible (d := d) (D := D) (W := W) (L := L) hD j)
  have hcolumns : Function.Injective columns := weightedSupportColumns_injective hD
  have hy₀ : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    have hy := y₀_le_two_mul_sub_one_of_eligible hD hg₁ (hband j)
    simpa [ν, SourceColumn.exponent_zero] using hy
  have hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν := by
    intro j
    have h := totalJetDegree_le_pred_of_weightedSupportEligible hD hcut (hband j)
    simpa [ν] using h
  have hdim : Module.finrank F (weightedSupportSpace F D d W L hD) = N := by
    rw [finrank_weightedSupportSpace_eq_card hD, ← Fintype.card_coe]
  have hmargin' : (543 / 500 : ℝ) * (r : ℝ) < N := by
    rw [← hdim]
    simpa only [r, Nat.cast_mul, mul_assoc] using hmargin
  have hrN : r < N := by
    have hrpos : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrlt : (r : ℝ) < N := by nlinarith
    exact_mod_cast hrlt
  have hrank :
      ((supportedLocalConstraintMatrix m (fun i => Polynomial.C (centers i)) w columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ r := by
    rw [rank_map_supportedLocalConstraintMatrix]
    exact localConstraintMatrix_rank_le_weightedSupport hD (fun i => centers i) w columns hband
  obtain ⟨cert⟩ := exists_certificate_of_rank_bound (L := L) (r := r)
    hL hbudget hkD centers w hw columns hcolumns hy₀ hdegree hband
    (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F)) hrank
    (by simpa only [Fintype.card_fin] using hrN)
  have hchallenge := kernel_height_lt_twelve_mul_of_margin N r (ℓ * ν)
    (Nat.mul_pos hℓ hν) hmargin'
  have hchallenge' : r * (ℓ * ν) / (N - r) ≤ 12 * (ℓ * ν) - 1 := by
    apply Nat.le_sub_one_of_lt
    exact_mod_cast hchallenge
  exact ⟨cert.weakenChallengeDegree (by
    simpa only [Fintype.card_fin] using hchallenge')⟩

/-- The prescribed rate interval constructs a polynomial-curve certificate. -/
theorem exists_weightedSupport_certificate_of_rate {F : Type*} [Field F]
    (δ : ℝ) (n D A k ℓ : ℕ) (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hn : 0 < n) (hD : 0 < D) (hρlo : δ / 3 ≤ (D : ℝ) / n)
    (hρhi : (D : ℝ) / n ≤ 1 - δ) (hkD : k ≤ D + 1)
    (hslack : (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤ A) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (Certificate A k ℓ (2 * m - 1) d
      (12 * (ℓ * (2 * m - 1)) - 1) centers w) := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let g₀ := rateGap δ ((D : ℝ) / n)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + theta * g₀) * d * m / H)
  have hρ : 0 < (D : ℝ) / n :=
    div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have hg := rateGap_pos hδ hρ
  have ho := prescribed_order_lower δ hδ hδmax
  have hHlo : xi / δ ≤ H := by simpa [H] using ho.2.2
  obtain ⟨hm, hW, _, _, _⟩ := prescribed_dimension_inputs δ _ H d hδ hδmax hρ hρhi
    (by omega) hHlo
  have hg₁ : g₀ ≤ 1 := rateGap_le_one δ _
  change (D : ℝ) * (1 + g₀) ≤ A at hslack
  have hA : 0 < A := by
    have : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) hslack
    exact_mod_cast this
  have hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast
    nlinarith
  have hmargin := prescribed_weightedSupport_margin (F := F) δ n D hδ hδmax hn hD
    hρlo hρhi
  change (543 / 500 : ℝ) * (n : ℝ) * Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
      (L := (m : ℝ) * D * (1 + g₀)) m hD 0 0)) <
    Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g₀)) hD) at hmargin
  rw [show (m : ℝ) * D = (D : ℝ) * m by ring] at hmargin
  have hmargin' : (543 / 500 : ℝ) * Fintype.card (Fin n) * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g₀)) hD) := by
    simpa only [Fintype.card_fin] using hmargin
  exact exists_certificate_of_fixed_margin (W := W) hD hg₁ hm hℓ hL
    (Nat.mul_pos hm hA) hkD centers w hw hmargin'

/-- The prescribed block threshold constructs a polynomial-curve certificate. -/
theorem exists_prescribed_certificate {F : Type*} [Field F] (δ : ℝ) (n k ℓ : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : ReedSolomon.capacityAgreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (Certificate (ReedSolomon.capacityAgreementThreshold δ n k) k ℓ (2 * m - 1) d
      (12 * (ℓ * (2 * m - 1)) - 1) centers w) := by
  let K := max k ⌊δ * n / 2⌋₊
  let D := K - 1
  have hA' : k + ⌈δ * n⌉₊ ≤ n := by
    simpa [ReedSolomon.capacityAgreementThreshold] using hA
  obtain ⟨hn, hD, _, hρlo, hρhi, _, hslack⟩ :=
    prescribedBlockBounds δ n k hδ hδmax.le hblock hA'
  have hkD : k ≤ D + 1 := by
    have hkK : k ≤ K := Nat.le_max_left _ _
    dsimp [D]
    omega
  have hcert := exists_weightedSupport_certificate_of_rate δ n D
    (ReedSolomon.capacityAgreementThreshold δ n k) k ℓ centers w hw hℓ hδ hδmax.le hn hD
    hρlo hρhi hkD hslack
  simpa only [xi] using hcert

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
