/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Harmonic
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Soundness
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Margin
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TotalJetDegreeRootCount
/-!
# The prescribed symbolic weighted-support certificate

The actual support margin produce a primitive symbolic interpolant with
challenge degree below `12(2m-1)` and total jet degree at most `2m-1`. It remains nonzero
at every challenge over every extension field and vanishes on every sufficiently close
Reed--Solomon polynomial. No matrix-rank or coefficient-height assumption remains.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26], Section 5.1, Corollary 5.3.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {d D m W N : ℕ} {g : ℝ}

/-- The prescribed strict support cutoff gives the integral total-jet-degree cap `2m - 1` on every
monomial occurring in the polynomial-coefficient interpolant. -/
theorem totalJetDegree_interpolant_le_two_mul_sub_one
    (hD : 0 < D) (hg : g ≤ 1) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W
      ((D : ℝ) * m * (1 + g)) (columns j).exponent)
    (v : Fin N → F[X]) :
    ∀ u ∈ (interpolant columns v).support, totalJetDegree u ≤ 2 * m - 1 := by
  have hQband : interpolant columns v ∈
      weightedSupportSpace F[X] D d W
        ((D : ℝ) * m * (1 + g)) hD := by
    rw [interpolant]
    apply Submodule.sum_mem
    intro j _
    rw [mem_weightedSupportSpace_iff]
    intro u hu
    have hueq : u = (columns j).exponent := by
      simpa using MvPolynomial.support_monomial_subset hu
    subst u
    exact hband j
  intro u hu
  have ht := totalJetDegree_lt_of_weightedSupportEligible hD
    (mem_weightedSupportSpace_iff.mp hQband u hu)
  have hquot :
      ((D : ℝ) * m * (1 + g)) / D ≤ (2 * m : ℕ) := by
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have heq : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
      field_simp
    rw [heq]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith
  have hnat : totalJetDegree u < 2 * m := by
    exact_mod_cast ht.trans_le hquot
  exact Nat.le_sub_one_of_lt hnat

/-- Every extension-field specialization has total jet degree at most `2m - 1`. -/
theorem jetTotalDegree_map_interpolant_le_two_mul_sub_one
    {E : Type*} [Field E] (hD : 0 < D) (hg : g ≤ 1)
    (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W
      ((D : ℝ) * m * (1 + g)) (columns j).exponent)
    (v : Fin N → F[X]) (ι : F →+* E) (z : E) :
    jetTotalDegree
      (MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v)) ≤ 2 * m - 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  have hQband := map_interpolant_mem_weightedSupportSpace hD columns hband v ι z
  have ht := totalJetDegree_lt_of_weightedSupportEligible hD
    (mem_weightedSupportSpace_iff.mp hQband u hu)
  have hquot :
      ((D : ℝ) * m * (1 + g)) / D ≤ (2 * m : ℕ) := by
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have heq : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
      field_simp
    rw [heq]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith
  have hnat : totalJetDegree u < 2 * m := by
    exact_mod_cast ht.trans_le hquot
  simpa [totalJetDegree, Finsupp.degree_eq_sum] using (Nat.le_sub_one_of_lt hnat)

/-- Bounds on the kernel coordinates give the same coefficientwise challenge-degree bound for
the assembled interpolant, including exponents outside the selected monomial columns. -/
theorem coeff_interpolant_natDegree_lt (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) (v : Fin N → F[X])
    {B : ℕ} (hB : 0 < B) (hv : ∀ j, (v j).natDegree < B) :
    ∀ u, (MvPolynomial.coeff u (interpolant columns v)).natDegree < B := by
  classical
  intro u
  by_cases hu : u ∈ Set.range (fun j ↦ (columns j).exponent)
  · obtain ⟨j, rfl⟩ := hu
    rw [coeff_interpolant columns hcolumns v j]
    exact hv j
  · have hcoeff : MvPolynomial.coeff u (interpolant columns v) = 0 := by
      rw [interpolant, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i heq
        exact (hu ⟨j, heq⟩).elim
      · rfl
    rw [hcoeff]
    simpa using hB

/-- The mathematical output of symbolic interpolation, with its certified challenge height. -/
structure Certificate (F : Type*) [Field F] {n : ℕ} (A k ν d h : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) where
  Q : DifferentialPolynomial F[X] d
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ ν
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ ν ∧
        ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k →
          A ≤ indices.card →
            (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
              differentialSpecialization
                (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Assemble the fixed-margin primitive kernel and the extension-field soundness theorem. -/
theorem exists_symbolic_weightedSupport_certificate_of_fixed_margin
    {A k : ℕ} {g₀ : ℝ} (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m)
    (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ))
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    {n : ℕ} (centers : Fin n ↪ F) (f g : Fin n → F)
    (hmargin : (543 / 500 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
           (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W
        ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (Certificate F A k (2 * m - 1) d (12 * (2 * m - 1) - 1) centers f g) := by
  let ν := 2 * m - 1
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hy₀ : ∀ u, WeightedSupportEligible D d W
      ((D : ℝ) * m * (1 + g₀)) u → u (some 0) ≤ ν := by
    intro u hu
    exact SymbolicWeightedSupportInterpolation.y₀_le_two_mul_sub_one_of_eligible
      hD hg₁ hm hu
  obtain ⟨v, _hv, _hkernel, _hvraw, hvheight, _hprimitive, hnozero,
      hconstraints, hband⟩ :=
    SymbolicWeightedSupportInterpolation.exists_symbolic_weightedSupport_interpolant_of_fixed_margin
      hD hν (fun i ↦ centers i) f g hy₀ hmargin
  let columns := SymbolicWeightedSupportInterpolation.weightedSupportColumns
    (d := d) (W := W)
      (L := (D : ℝ) * m * (1 + g₀)) hD
  let Q : DifferentialPolynomial F[X] d := interpolant columns v
  have hvheightNat : ∀ j, (v j).natDegree < 12 * ν := by
    intro j
    exact_mod_cast hvheight j
  have hchallenge : ∀ u, (MvPolynomial.coeff u Q).natDegree < 12 * ν := by
    dsimp only [Q]
    exact coeff_interpolant_natDegree_lt columns
      (SymbolicWeightedSupportInterpolation.weightedSupportColumns_injective hD) v
        (Nat.mul_pos (by omega) hν) hvheightNat
  have htotal : ∀ u ∈ Q.support, totalJetDegree u ≤ ν := by
    dsimp only [Q, ν]
    exact totalJetDegree_interpolant_le_two_mul_sub_one hD hg₁ columns hband v
  refine ⟨⟨Q, fun u ↦ Nat.le_sub_one_of_lt (hchallenge u), htotal, ?_⟩⟩
  intro E _ ι z
  refine ⟨by simpa only [Q] using hnozero ι z, ?_, ?_⟩
  · simpa only [Q, ν] using
      jetTotalDegree_map_interpolant_le_two_mul_sub_one hD hg₁ columns hband v ι z
  · intro indices P hP hcard hagreements
    simpa only [Q] using
      differentialSpecialization_map_interpolant_eq_zero_of_degree_lt
        hD hL hbudget hkD (fun i ↦ centers i) f g columns hband v hconstraints
          ι z indices P hP centers.injective.injOn hcard hagreements

open SimplexIntegration WeightedSupportParameters

/-- The prescribed no-band support constructs a symbolic line certificate from the rate interval
and agreement cutoff. Every dimension and rank premise is proved by the support construction. -/
theorem exists_weightedSupport_certificate_of_rate {F : Type*} [Field F]
    (δ : ℝ) (n D A k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hn : 0 < n) (hD : 0 < D)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hkD : k ≤ D + 1)
    (hslack : (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤ A) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicPowerSum (d - 1) 1)
    Nonempty (Certificate F A k (2 * m - 1) d (12 * (2 * m - 1) - 1) centers f g) := by
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
  apply exists_symbolic_weightedSupport_certificate_of_fixed_margin (W := W)
    hD hg.2 hm hL (Nat.mul_pos hm hA) hkD centers f g
  change (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
      (L := (m : ℝ) * D * (1 + g₀)) m hD 0 0)) <
    Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g₀)) hD) at hmargin
  rw [show (m : ℝ) * D * (1 + g₀) = D * m * (1 + g₀) by ring] at hmargin
  exact hmargin

/-- The prescribed block threshold supplies a uniformly nonvanishing line certificate. -/
theorem exists_prescribed_symbolic_weightedSupport_certificate {F : Type*} [Field F]
    (δ : ℝ) (n k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    Nonempty (Certificate F (agreementThreshold δ n k) k (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers f g) := by
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
    (agreementThreshold δ n k) k centers f g hδ hδmax.le hn hD hρlo hρhi hkD hslack
  simpa only [xi, harmonicPowerSum_one, harmonicNumber_eq_harmonic] using hc

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
