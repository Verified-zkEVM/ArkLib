/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold

/-!
# Certificates from symbolic weighted-support interpolation

A symbolic weighted-support certificate is a differential polynomial whose challenge
specializations stay nonzero, have bounded total jet degree, satisfy the local constraints at every
received point, and vanish on every sufficiently agreeing message polynomial. A strict dimension
surplus constructs such a certificate for received lines; the prescribed rate parameters provide
the surplus and the corresponding degree bounds.

## Main statements

* `WeightedSupportCertificate`: the challenge-degree, total-jet-degree and specialization
  properties of a symbolic certificate.
* `exists_weightedSupport_certificate_of_fixed_margin`: construction from a weighted-support
  surplus.
* `exists_weightedSupport_certificate_of_rate` and
  `exists_prescribed_symbolic_weightedSupport_certificate`: the rate-parameter constructions.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26], Section 5.1, Corollary 5.3.
-/

@[expose] public section

open Polynomial PolynomialDifferential
open MvPolynomial
open ReedSolomon.HiddenDerivative.WeightedSupportParameters
open scoped BigOperators

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- A differential polynomial over `F[X]` whose challenge specializations remain nonzero, have
bounded total jet degree and vanish on sufficiently agreeing message polynomials. -/
structure WeightedSupportCertificate (F : Type*) [Field F] {ι : Type*} [Fintype ι]
    (A k ν d h : ℕ) (centers : ι ↪ F) (f g : ι → F) where
  /-- The differential polynomial with challenge-polynomial coefficients. -/
  interpolant : DifferentialPolynomial F[X] d
  /-- Every coefficient of the interpolant has challenge degree at most `h`. -/
  challengeDegree_le : ∀ u, (interpolant.coeff u).natDegree ≤ h
  /-- Every monomial of the interpolant has total jet degree at most `ν`. -/
  totalJetDegree_le : ∀ u ∈ interpolant.support, totalJetDegree u ≤ ν
  /-- Every challenge specialization is nonzero, has total jet degree at most `ν`, and vanishes on
  every polynomial of degree below `k` that agrees with the received line at at least `A` points. -/
  specialization_sound : ∀ {E : Type*} [Field E] (embed : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom embed z) interpolant ≠ 0 ∧
      jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom embed z) interpolant) ≤ ν ∧
        ∀ (indices : Finset ι) (P : E[X]), P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (embed (centers i)) = embed (f i) + z * embed (g i)) →
            differentialSpecialization
              (MvPolynomial.map (Polynomial.eval₂RingHom embed z) interpolant) P = 0

private theorem satisfiesLocalConstraints_map_coefficients {F E : Type*} [Field F]
    [CommRing E] {d m : ℕ} (φ : F[X] →+* E) (center received : F[X])
    (Q : DifferentialPolynomial F[X] d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  rw [satisfiesLocalConstraints_iff_coeff_eq_zero] at hQ ⊢
  intro e he
  rw [← map_unscaledLocalSubstitution φ center received Q, MvPolynomial.coeff_map]
  simpa using congrArg φ (hQ e he)

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
    Nonempty (WeightedSupportCertificate F A k (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers f g) := by
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
    have hDm : 0 ≤ (D : ℝ) * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      (D : ℝ) * m * (1 + g₀) ≤ (D : ℝ) * m * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hg₁]) hDm
      _ = (D : ℝ) * ((2 * m : ℕ) : ℝ) := by push_cast; ring
  have hν : 0 < 2 * m - 1 := by omega
  have hy₀ : ∀ j : ↥support, (columns j).y₀ ≤ 2 * m - 1 := by
    intro j
    have ht := totalJetDegree_le_pred_of_weightedSupportEligible (t := 2 * m) hD
      (by exact_mod_cast hcut)
      (hband j)
    rw [SourceColumn.totalJetDegree_exponent] at ht
    exact (Nat.le_add_right _ _).trans ht
  let localRank := Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0))
  have hmargin' : (543 / 500 : ℝ) * Fintype.card ι * localRank <
      Module.finrank F (weightedSupportSpace F D d W L hD) := by
    simpa [localRank, L] using hmargin
  have hmarginCard : Fintype.card ι * localRank < support.card := by
    rw [finrank_weightedSupportSpace_eq_card hD] at hmargin'
    have hreal : (Fintype.card ι : ℝ) * localRank < (support.card : ℝ) := by
      nlinarith [hmargin']
    have hreal' : ((Fintype.card ι * localRank : ℕ) : ℝ) <
        (Fintype.card (↥support) : ℝ) := by
      simpa only [Fintype.card_coe, Nat.cast_mul] using hreal
    have hnat := Nat.cast_lt.mp hreal'
    simpa only [Fintype.card_coe] using hnat
  obtain ⟨v, _hv, hvheight, _hspan, hvnonzero, hconstraints⟩ :=
    exists_primitive_weightedSupport_interpolant (L := L) (W := W)
      (κ := ↥support) hD m 1 (2 * m - 1) (fun i => centers i)
      (fun i => receivedLine (f i) (g i))
      (fun i => natDegree_receivedLine_le (f i) (g i)) columns hcolumns hy₀ hband
      (by simpa [localRank] using hmarginCard)
  let rankBound := Fintype.card ι * localRank
  let supportCard := Fintype.card (↥support)
  have hmarginReal : (543 / 500 : ℝ) * (rankBound : ℝ) < (supportCard : ℝ) := by
    have h := hmargin'
    rw [finrank_weightedSupportSpace_eq_card hD] at h
    have hcast : (rankBound : ℝ) = (Fintype.card ι : ℝ) * localRank := by
      simp [rankBound, Nat.cast_mul]
    rw [hcast]
    calc
      (543 / 500 : ℝ) * ((Fintype.card ι : ℝ) * localRank) =
          (543 / 500 : ℝ) * Fintype.card ι * localRank := by ring
      _ < (supportCard : ℝ) := by
        simpa [supportCard, support, Fintype.card_coe] using h
  have hratio : rankBound * (2 * m - 1) /
      (supportCard - rankBound) < 12 * (2 * m - 1) := by
    have hrankLt : rankBound < supportCard := by
      simpa [supportCard, Fintype.card_coe] using hmarginCard
    have hden : 0 < supportCard - rankBound := Nat.sub_pos_of_lt hrankLt
    have hratioNat : rankBound < 12 * (supportCard - rankBound) := by
      have hstrong : (13 : ℝ) * rankBound < 12 * supportCard := by
        have hr0 : (0 : ℝ) ≤ rankBound := Nat.cast_nonneg _
        nlinarith [hmarginReal, hr0]
      have hstrongNat : 13 * rankBound < 12 * supportCard := by exact_mod_cast hstrong
      omega
    have hnumerator : rankBound * (2 * m - 1) <
        (12 * (2 * m - 1)) * (supportCard - rankBound) := by
      calc
        rankBound * (2 * m - 1) < (12 * (supportCard - rankBound)) * (2 * m - 1) :=
          Nat.mul_lt_mul_of_pos_right hratioNat hν
        _ = (12 * (2 * m - 1)) * (supportCard - rankBound) := by ring
    exact (Nat.div_lt_iff_lt_mul hden).2 hnumerator
  have hvheight' : ∀ j : ↥support, (v j).natDegree < 12 * (2 * m - 1) := by
    intro j
    have h := hvheight j
    exact h.trans_lt (by simpa [rankBound, supportCard] using hratio)
  have hchallenge : ∀ u, ((SourceColumn.interpolant columns v).coeff u).natDegree <
      12 * (2 * m - 1) :=
    SourceColumn.coeff_interpolant_natDegree_lt hcolumns v (by omega) hvheight'
  let Q := SourceColumn.interpolant columns v
  have hQspace : Q ∈ weightedSupportSpace F[X] D d W L hD := by
    dsimp [Q]
    exact interpolant_mem_weightedSupportSpace hD columns hband v
  refine ⟨⟨Q, fun u => Nat.le_sub_one_of_lt (hchallenge u), ?_, ?_⟩⟩
  · intro u hu
    exact totalJetDegree_interpolant_le_two_mul_sub_one hD hg₁ columns hband v u hu
  · intro E _ embed z
    let φ : F[X] →+* E := Polynomial.eval₂RingHom embed z
    let Qz : DifferentialPolynomial E d := MvPolynomial.map φ Q
    have hQzspace : Qz ∈ weightedSupportSpace E D d W L hD := by
      dsimp [Qz, φ, Q]
      exact map_interpolant_mem_weightedSupportSpace hD columns hband v φ
    have hjet : jetTotalDegree Qz ≤ 2 * m - 1 := by
      simpa [Qz, Q, φ] using
        jetTotalDegree_map_interpolant_le_two_mul_sub_one hD hg₁ columns hband v embed z
    refine ⟨?_, hjet, ?_⟩
    · simpa [Qz, φ, Q] using hvnonzero φ
    · intro indices P hP hcard hagreements
      have hdegree : differentialWeightedDegree D Qz < m * A :=
        differentialWeightedDegree_lt_of_mem_weightedSupportSpace hbudget hL hQzspace
      have hconstraintsE : ∀ i ∈ indices,
          SatisfiesLocalConstraints m (embed (centers i))
            (embed (f i) + z * embed (g i)) Qz := by
        intro i hi
        have h := satisfiesLocalConstraints_map_coefficients φ
          (Polynomial.C (centers i)) (receivedLine (f i) (g i)) Q (hconstraints i)
        have h' : SatisfiesLocalConstraints m (embed (centers i))
            (embed (f i) + embed (g i) * z) Qz := by
          simpa [φ, Qz, Q, receivedLine] using h
        rw [mul_comm] at h'
        exact h'
      have hPdegree : P.natDegree ≤ D := by
        by_cases hPzero : P = 0
        · simp [hPzero]
        · have hPnat : P.natDegree < k :=
            (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hP
          omega
      have hembed : Function.Injective embed := RingHom.injective embed
      have hinj : Set.InjOn (fun i => embed (centers i)) (↑indices) := by
        intro i hi j hj hij
        apply centers.injective
        exact hembed hij
      exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
        (fun i => embed (centers i))
        (fun i => embed (f i) + z * embed (g i)) indices hdegree hconstraintsE P hPdegree
        hinj hcard hagreements

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
    Nonempty (WeightedSupportCertificate F A k (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers f g) := by
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
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : ReedSolomon.agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (WeightedSupportCertificate F (ReedSolomon.agreementThreshold δ n k) k
      (2 * m - 1) d (12 * (2 * m - 1) - 1) centers f g) := by
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
