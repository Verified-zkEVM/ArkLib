/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold

/-!
# Weighted-support certificate constructions

This module constructs certificates for received lines using the symbolic curve certificate API.
The weighted-support interpolation construction imposes local constraints at every received point;
a strict dimension surplus yields challenge-degree and jet-degree bounds, and prescribed rate
parameters provide the surplus for the certificate construction.

## Main statements

* `exists_weightedSupport_certificate_of_fixed_margin`: construction from a weighted-support
  dimension surplus.
* `exists_weightedSupport_certificate_of_rate` and
  `exists_prescribed_symbolic_weightedSupport_certificate`: the rate-parameter constructions.

## References

* [DKTZ26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open MvPolynomial
open ReedSolomon.HiddenDerivative.WeightedSupportParameters
open scoped BigOperators

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- A strict weighted-support surplus constructs a certificate for any received line. -/
theorem exists_weightedSupport_certificate_of_fixed_margin {F : Type*} [Field F]
    {D d W m : ℕ} {ι : Type*} [Fintype ι] {A k : ℕ} {g₀ : ℝ}
    (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m)
    (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    (hkD : k ≤ D + 1) (centers : ι ↪ F) (f g : ι → F)
    (hmargin : (543 / 500 : ℝ) * Fintype.card ι * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0)) <
      Module.finrank F
        (weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (SymbolicReceivedCurve.Certificate A k 1 (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers (fun i => receivedLine (f i) (g i))) := by
  let L : ℝ := (D : ℝ) * m * (1 + g₀)
  let support := weightedSupportExponents D d W L hD
  let columns : ↥support → SourceColumn d := fun u => SourceColumn.ofExponent u.1
  have hcolumns : Function.Injective columns := by
    intro u v huv
    apply Subtype.ext
    have h := congrArg SourceColumn.exponent huv
    simpa [columns] using h
  have hband : ∀ j : ↥support, WeightedSupportEligible D d W L
      (columns j).exponent := by
    intro j
    simpa [columns] using (mem_weightedSupportExponents.mp j.2)
  have hcut : L ≤ (D : ℝ) * ((2 * m : ℕ) : ℝ) := by
    dsimp [L]
    exact weightedSupportCutoff_le_two_mul D m hg₁
  let ν := 2 * m - 1
  have hν : 0 < ν := by dsimp [ν]; omega
  have hy₀ : ∀ j : ↥support, (columns j).y₀ ≤ ν := by
    intro j
    have hy := y₀_le_two_mul_sub_one_of_eligible hD hg₁ (hband j)
    simpa [ν, SourceColumn.exponent_zero] using hy
  have hdegree : ∀ j : ↥support, totalJetDegree (columns j).exponent ≤ ν := by
    intro j
    have h := totalJetDegree_le_pred_of_weightedSupportEligible hD hcut (hband j)
    simpa [ν] using h
  let localRank := Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0))
  let rankBound := Fintype.card ι * localRank
  let supportCard := support.card
  have hmarginSpace : (543 / 500 : ℝ) * Fintype.card ι * localRank <
      Module.finrank F (weightedSupportSpace F D d W L hD) := by
    simpa [localRank, L] using hmargin
  have hmarginReal : (543 / 500 : ℝ) * (rankBound : ℝ) < (supportCard : ℝ) := by
    rw [finrank_weightedSupportSpace_eq_card hD] at hmarginSpace
    have hcast : (rankBound : ℝ) = (Fintype.card ι : ℝ) * localRank := by
      simp [rankBound, Nat.cast_mul]
    rw [hcast]
    calc
      (543 / 500 : ℝ) * ((Fintype.card ι : ℝ) * localRank) =
          (543 / 500 : ℝ) * Fintype.card ι * localRank := by ring
      _ < (supportCard : ℝ) := by
        simpa [supportCard, support, Fintype.card_coe] using hmarginSpace
  have hmarginCard : rankBound < supportCard := by
    have hscale : (rankBound : ℝ) ≤ (543 / 500 : ℝ) * rankBound := by
      have hnonneg : (0 : ℝ) ≤ rankBound := Nat.cast_nonneg _
      nlinarith
    have hlt : (rankBound : ℝ) < supportCard := hscale.trans_lt hmarginReal
    exact_mod_cast hlt
  have hrank :
      ((supportedLocalConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ rankBound := by
    rw [rank_map_supportedLocalConstraintMatrix (algebraMap F[X] (RatFunc F)) m _ _ _]
    simpa [rankBound, localRank, L] using
      localConstraintMatrix_rank_le_weightedSupport (F := F) (d := d) (D := D) (m := m)
        (W := W) (L := L) hD (fun i => centers i)
        (fun i => receivedLine (f i) (g i)) columns hband
  obtain ⟨cert⟩ := SymbolicReceivedCurve.exists_certificate_of_rank_bound
    (L := L) (r := rankBound) hL hbudget hkD centers
    (fun i => receivedLine (f i) (g i))
    (fun i => natDegree_receivedLine_le (f i) (g i)) columns hcolumns hy₀ hdegree hband
    (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F)) hrank
    (by simpa [supportCard, Fintype.card_coe] using hmarginCard)
  have hchallengeReal := kernel_height_lt_twelve_mul_of_margin supportCard rankBound ν hν
    (by simpa [supportCard] using hmarginReal)
  have hchallenge : rankBound * ν / (supportCard - rankBound) < 12 * ν := by
    exact_mod_cast hchallengeReal
  have hchallenge' : rankBound * (1 * ν) / (supportCard - rankBound) ≤ 12 * ν - 1 := by
    have hle : rankBound * ν / (supportCard - rankBound) ≤ 12 * ν - 1 := by omega
    simpa only [Nat.one_mul] using hle
  exact ⟨cert.weakenChallengeDegree (by
    simpa [ν, support, Fintype.card_coe] using hchallenge')⟩

/-- The prescribed rate interval constructs a certificate with challenge degree below
`12 (2 m - 1)` and total jet degree at most `2 m - 1`. -/
theorem exists_weightedSupport_certificate_of_rate {F : Type*} [Field F]
    (δ : ℝ) (n D A k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hn : 0 < n) (hD : 0 < D)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hkD : k ≤ D + 1)
    (hslack : (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤ A) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (SymbolicReceivedCurve.Certificate A k 1 (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers (fun i => receivedLine (f i) (g i))) := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let g₀ := rateGap δ ((D : ℝ) / n)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + theta * g₀) * d * m / H)
  have hρ : 0 < (D : ℝ) / n :=
    div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have hg : 0 < g₀ := rateGap_pos hδ hρ
  obtain ⟨hd, _, hHlo⟩ := prescribed_order_lower δ hδ hδmax
  have hHlo' : xi / δ ≤ H := by simpa [H] using hHlo
  obtain ⟨hm, hW, _, _, _⟩ := prescribed_dimension_inputs δ _ H d hδ hδmax hρ hρhi
    (by omega) hHlo'
  have hA : 0 < A := by
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have hA' : (0 : ℝ) < (A : ℝ) := by
      exact (mul_pos hDR (by linarith)).trans_le hslack
    exact_mod_cast hA'
  have hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m)
    push_cast
    nlinarith
  have hmargin := prescribed_weightedSupport_margin (F := F) δ n D hδ hδmax hn hD
    hρlo hρhi
  change (543 / 500 : ℝ) * (n : ℝ) * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g₀)) m hD 0 0)) <
      Module.finrank F
        (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g₀)) hD) at hmargin
  rw [show (m : ℝ) * D = (D : ℝ) * m by ring] at hmargin
  exact exists_weightedSupport_certificate_of_fixed_margin (d := d) (m := m) (W := W) hD
    (rateGap_le_one δ ((D : ℝ) / n)) hm hL (Nat.mul_pos hm hA) hkD centers f g
    (by simpa only [Fintype.card_fin] using hmargin)

/-- The prescribed block threshold constructs a uniformly nonvanishing line certificate. -/
theorem exists_prescribed_symbolic_weightedSupport_certificate {F : Type*} [Field F]
    (δ : ℝ) (n k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : ReedSolomon.agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (SymbolicReceivedCurve.Certificate (ReedSolomon.agreementThreshold δ n k) k 1
      (2 * m - 1) d (12 * (2 * m - 1) - 1) centers
      (fun i => receivedLine (f i) (g i))) := by
  let D := max k ⌊δ * n / 2⌋₊ - 1
  have hA' : k + ⌈δ * n⌉₊ ≤ n := by
    simpa [ReedSolomon.agreementThreshold] using hA
  obtain ⟨hn, hD, _, hρlo, hρhi, _, hslack⟩ :=
    prescribedBlockBounds δ n k hδ hδmax.le hblock hA'
  have hkD : k ≤ D + 1 := by
    dsimp [D]
    omega
  have hslack' : (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤
      ReedSolomon.agreementThreshold δ n k := by
    simpa [D, ReedSolomon.agreementThreshold] using hslack
  have hcert := exists_weightedSupport_certificate_of_rate δ n D
    (ReedSolomon.agreementThreshold δ n k) k centers f g hδ hδmax.le hn hD hρlo hρhi hkD
    hslack'
  simpa [ReedSolomon.agreementThreshold] using hcert

end ReedSolomon.HiddenDerivative
