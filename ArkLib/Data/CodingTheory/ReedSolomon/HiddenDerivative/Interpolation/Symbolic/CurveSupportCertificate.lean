/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveWeightedSupport
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.SupportCertificate

/-!
# Symbolic curve certificates at capacity parameters

The same no-band support works for received polynomial curves of every positive
degree `ℓ`. Its total jet degree is unchanged, and its challenge-degree cap is multiplied by
`ℓ`. The interpolant is nonzero at every challenge over every extension field and vanishes
on every sufficiently agreeing polynomial of degree below the message dimension.

This is the interpolation input to polynomial-curve correlated agreement, not the geometric
curve-transfer theorem itself.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), symbolic interpolation for polynomial
  curves.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

variable {F : Type*} [Field F] {d D m W : ℕ}

/-- A uniformly nonvanishing symbolic differential equation for a received polynomial curve.
The certified challenge height `h` is independent of the derivative-variable cap `ν`.
The prescribed constructor instantiates it at `12 * (ℓ * ν) - 1`. -/
structure Certificate (F : Type*) [Field F] {n : ℕ} (A k ℓ ν d h : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) where
  Q : DifferentialPolynomial F[X] d
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ ν
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ ν ∧
    ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
      (∀ i ∈ indices, P.eval (ι (centers i)) = (w i).eval₂ ι z) →
      differentialSpecialization (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Assemble curve interpolation and soundness from the fixed dimension margin. No matrix
rank, primitive-vector, or extension-field soundness premise is left to the caller. -/
theorem exists_certificate_of_fixed_margin {n A k ℓ : ℕ} {g₀ : ℝ}
    (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m) (hℓ : 0 < ℓ)
    (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ))
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hmargin : (543 / 500 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
           (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W
        ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (Certificate F A k ℓ (2 * m - 1) d (12 * (ℓ * (2 * m - 1)) - 1) centers w) := by
  let ν := 2 * m - 1
  let columns := weightedSupportColumns (d := d) (W := W)
     (L := (D : ℝ) * m * (1 + g₀)) hD
  let N := Fintype.card (WeightedSupportIndex D d W
    ((D : ℝ) * m * (1 + g₀)) hD)
  let r := n * Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
       (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0))
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hband : ∀ j, WeightedSupportEligible D d W
      ((D : ℝ) * m * (1 + g₀)) (columns j).exponent := weightedSupportColumns_eligible hD
  have hcolumns : Function.Injective columns := weightedSupportColumns_injective hD
  have hy₀ : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    simpa [SourceColumn.exponent] using
      y₀_le_two_mul_sub_one_of_eligible hD hg₁ hm (hband j)
  have hdim : Module.finrank F (weightedSupportSpace F D d W
      ((D : ℝ) * m * (1 + g₀)) hD) = N := by
    rw [finrank_weightedSupportSpace_eq_card hD, ← Fintype.card_coe]
  have hmargin' : (543 / 500 : ℝ) * (r : ℝ) < N := by
    rw [← hdim]
    simpa only [r, Nat.cast_mul, mul_assoc] using hmargin
  have hrN : r < N := by
    have hrpos : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrlt : (r : ℝ) < N := by nlinarith
    exact_mod_cast hrlt
  obtain ⟨v, _hv, hvdeg, _hp, hnozero, hconstraints⟩ :=
    exists_primitive_weightedSupport_interpolant hD ℓ ν (fun i ↦ centers i) w hw
      columns hcolumns hy₀ hband hrN
  have hvheight : ∀ j, (v j).natDegree < 12 * (ℓ * ν) := by
    intro j
    have hle : ((v j).natDegree : ℝ) ≤ ((r * (ℓ * ν) / (N - r) : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr (show (v j).natDegree ≤ r * (ℓ * ν) / (N - r) from hvdeg j)
    have hlt := hle.trans_lt
      (noBand_kernel_height_lt N r (ℓ * ν) (Nat.mul_pos hℓ hν) hmargin')
    exact_mod_cast hlt
  let Q : DifferentialPolynomial F[X] d := interpolant columns v
  refine ⟨⟨Q, ?_, ?_, ?_⟩⟩
  · intro u
    exact Nat.le_sub_one_of_lt (coeff_interpolant_natDegree_lt columns hcolumns v
      (Nat.mul_pos (by omega) (Nat.mul_pos hℓ hν)) hvheight u)
  · exact totalJetDegree_interpolant_le_two_mul_sub_one hD hg₁ columns hband v
  · intro E _ ι z
    refine ⟨hnozero ι z, ?_, ?_⟩
    · exact jetTotalDegree_map_interpolant_le_two_mul_sub_one hD hg₁ columns hband v ι z
    · intro indices P hP hcard hagreements
      have hPnat : P.natDegree ≤ D := by
        by_cases hz : P = 0
        · simp [hz]
        · have hk : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
          omega
      exact differentialSpecialization_curve_interpolant_eq_zero_of_agreements
        hD hL hbudget (fun i ↦ centers i) w columns hband v hconstraints
        ι z indices P hPnat centers.injective.injOn hcard hagreements

open SimplexIntegration WeightedSupportParameters

/-- The prescribed no-band support constructs the curve equation from the rate interval and
agreement cutoff, with no matrix-rank or coefficient-height hypothesis. -/
theorem exists_weightedSupport_certificate_of_rate {F : Type*} [Field F]
    (δ : ℝ) (n D A k ℓ : ℕ) (centers : Fin n ↪ F) (w : Fin n → Polynomial F)
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hn : 0 < n) (hD : 0 < D)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hkD : k ≤ D + 1)
    (hslack : (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤ A) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicPowerSum (d - 1) 1)
    Nonempty (Certificate F A k ℓ (2 * m - 1) d (12 * (ℓ * (2 * m - 1)) - 1) centers w) := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let H := harmonicPowerSum (d - 1) 1
  let g₀ := rateGap δ ((D : ℝ) / n)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + theta * g₀) * d * m / H)
  have hρ : 0 < (D : ℝ) / n := div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have hg := clippedGap_mem_unit δ _ hδ hρ
  have ho := prescribed_order_lower δ hδ hδmax
  have hHlo : xi / δ ≤ H := by simpa only [H, harmonicPowerSum_one] using ho.2.2
  have hp := prescribed_dimension_inputs δ _ H d hδ hδmax hρ hρhi ho.1 hHlo
  have hm : 0 < m := hp.1
  have hg0 : 0 < g₀ := hg.1
  change (D : ℝ) * (1 + g₀) ≤ A at hslack
  have hA : 0 < A := by
    have : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) hslack
    exact_mod_cast this
  have hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast
    nlinarith
  have hmargin := prescribed_weightedSupport_margin (F := F) δ n D hδ hδmax hn hD hρlo hρhi
  apply exists_certificate_of_fixed_margin (W := W)
    hD hg.2 hm hℓ hL (Nat.mul_pos hm hA) hkD centers w hw
  change (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
      (L := (m : ℝ) * D * (1 + g₀)) m hD 0 0)) <
    Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g₀)) hD) at hmargin
  rw [show (m : ℝ) * D * (1 + g₀) = D * m * (1 + g₀) by ring] at hmargin
  exact hmargin

/-- The prescribed block threshold constructs the height-bounded polynomial-curve certificate. -/
theorem exists_prescribed_certificate {F : Type*} [Field F]
    (δ : ℝ) (n k ℓ : ℕ) (centers : Fin n ↪ F) (w : Fin n → Polynomial F)
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    Nonempty (Certificate F (agreementThreshold δ n k) k ℓ (2 * m - 1) d
      (12 * (ℓ * (2 * m - 1)) - 1) centers w) := by
  let K := max k (Nat.floor (δ * n / 2))
  let D := K - 1
  have hb := prescribedBlockBounds δ n k hδ hδmax hk
    (by simpa only [xi, harmonicNumber_eq_harmonic] using hblock) hA
  obtain ⟨hn, hD, _, hρlo, hρhi, _, hslack⟩ := hb
  have hkD : k ≤ D + 1 := by
    have hh : k ≤ K := Nat.le_max_left _ _
    have hK : 0 < K := hk.trans_le hh
    dsimp [D]
    omega
  have hc := exists_weightedSupport_certificate_of_rate δ n D
    (agreementThreshold δ n k) k ℓ centers w hw hℓ hδ hδmax.le hn hD hρlo hρhi hkD hslack
  simpa only [xi, harmonicPowerSum_one, harmonicNumber_eq_harmonic] using hc

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
