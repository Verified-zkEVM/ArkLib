/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate

/-!
# Symbolic interpolation with a variable rank margin

The finite weighted support has `N` monomials and stacked local rank at most `r`.
When `r < N`, the primitive polynomial kernel has challenge height at most
`r * (ℓ * ν) / (N - r)`. Here `ℓ` is the received-curve degree and `ν` is an
independent total jet bound. Neither is determined by the interpolation multiplicity.

This constructor separates the algebraic certificate from the analytic rate gate:
the rate estimates supply the finite surplus, while the same certificate serves
list decoding and exact correlated agreement over arbitrary fields.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open MvPolynomial

/-- A bound on each selected monomial bounds the assembled polynomial, regardless of its
coefficient polynomials. -/
theorem totalJetDegree_interpolant_le {F : Type*} [Field F] {d N ν : ℕ}
    (columns : Fin N → SourceColumn d)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (vector : Fin N → F[X]) :
    ∀ exponent ∈ (interpolant columns vector).support, totalJetDegree exponent ≤ ν := by
  classical
  intro exponent hexponent
  obtain ⟨index, _, hindex⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hexponent)
  have heq : exponent = (columns index).exponent := by
    simpa using MvPolynomial.support_monomial_subset hindex
  subst exponent
  exact hdegree index

/-- Specializing coefficient polynomials cannot increase the total jet bound. -/
theorem jetTotalDegree_map_interpolant_le {F E : Type*} [Field F] [Field E]
    {d N ν : ℕ} (columns : Fin N → SourceColumn d)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (vector : Fin N → F[X]) (embedding : F →+* E) (challenge : E) :
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom embedding challenge)
      (interpolant columns vector)) ≤ ν := by
  rw [jetTotalDegree_le_iff]
  intro exponent hexponent
  have hsource := MvPolynomial.support_map_subset _ _ hexponent
  simpa [totalJetDegree, Finsupp.degree_eq_sum] using
    totalJetDegree_interpolant_le columns hdegree vector exponent hsource

/-- Coordinatewise polynomial degree bounds pass to every coefficient of the interpolant. -/
theorem coeff_interpolant_natDegree_le {F : Type*} [Field F] {d N height : ℕ}
    (columns : Fin N → SourceColumn d) (hinjective : Function.Injective columns)
    (vector : Fin N → F[X]) (hheight : ∀ index, (vector index).natDegree ≤ height) :
    ∀ exponent, (MvPolynomial.coeff exponent (interpolant columns vector)).natDegree ≤ height := by
  intro exponent
  exact Nat.lt_succ_iff.mp (coeff_interpolant_natDegree_lt columns hinjective vector
    (Nat.succ_pos height) (fun index ↦ Nat.lt_succ_iff.mpr (hheight index)) exponent)

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

/-- A finite dimension surplus constructs a curve certificate with its exact integer kernel
height. The caller supplies support bounds, not a polynomial or a soundness assumption. -/
theorem exists_certificate_of_surplus {F : Type*} [Field F]
    {d D m W n A k ℓ ν : ℕ} {cutoff : ℝ}
    (hD : 0 < D) (hcutoff : cutoff ≤ (m * A : ℕ))
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ index, (received index).natDegree ≤ ℓ)
    (hdegree : ∀ exponent, WeightedSupportEligible D d W cutoff exponent →
      totalJetDegree exponent ≤ ν)
    (hsurplus : n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := cutoff) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W cutoff hD)) :
    let count := Module.finrank F (weightedSupportSpace F D d W cutoff hD)
    let rank := n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := cutoff) m hD 0 0))
    Nonempty (Certificate F A k ℓ ν d (rank * (ℓ * ν) / (count - rank))
      centers received) := by
  classical
  let columns := weightedSupportColumns (d := d) (W := W) (L := cutoff) hD
  let count := Fintype.card (WeightedSupportIndex D d W cutoff hD)
  have hdimension : Module.finrank F (weightedSupportSpace F D d W cutoff hD) = count := by
    rw [finrank_weightedSupportSpace_eq_card hD, ← Fintype.card_coe]
  have hband : ∀ index, WeightedSupportEligible D d W cutoff (columns index).exponent :=
    weightedSupportColumns_eligible hD
  have hcolumns := weightedSupportColumns_injective (d := d) (W := W) (L := cutoff) hD
  have htotal : ∀ index, totalJetDegree (columns index).exponent ≤ ν :=
    fun index ↦ hdegree _ (hband index)
  have hy₀ : ∀ index, (columns index).y₀ ≤ ν := by
    intro index
    have hcoordinate : (columns index).exponent (some 0) ≤
        totalJetDegree (columns index).exponent :=
      Finsupp.le_degree 0 (columns index).exponent.some
    exact (by simpa [SourceColumn.exponent] using hcoordinate :
      (columns index).y₀ ≤ totalJetDegree (columns index).exponent).trans (htotal index)
  rw [hdimension] at hsurplus ⊢
  obtain ⟨vector, _, hheight, _, hnonzero, hconstraints⟩ :=
    exists_primitive_weightedSupport_interpolant hD ℓ ν (fun index ↦ centers index)
      received hreceived columns hcolumns hy₀ hband hsurplus
  refine ⟨⟨interpolant columns vector,
    coeff_interpolant_natDegree_le columns hcolumns vector hheight,
    totalJetDegree_interpolant_le columns htotal vector, ?_⟩⟩
  intro E _ embedding challenge
  refine ⟨hnonzero embedding challenge,
    jetTotalDegree_map_interpolant_le columns htotal vector embedding challenge, ?_⟩
  intro indices polynomial hpolynomial hcard hagreement
  have hnat : polynomial.natDegree ≤ D := by
    by_cases hzero : polynomial = 0
    · simp [hzero]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hpolynomial
      omega
  exact differentialSpecialization_curve_interpolant_eq_zero_of_agreements
    hD hcutoff hbudget (fun index ↦ centers index) received columns hband vector hconstraints
    embedding challenge indices polynomial hnat centers.injective.injOn hcard hagreement

/-- Any real source/rank ratio above one bounds the integer kernel height. -/
theorem kernel_height_lt_of_ratio {count rank budget : ℕ} {gamma : ℝ}
    (hgamma : 1 < gamma) (hbudget : 0 < budget)
    (hmargin : gamma * rank < count) :
    ((rank * budget / (count - rank) : ℕ) : ℝ) < (budget : ℝ) / (gamma - 1) := by
  have hrank : (rank : ℝ) < count := by
    nlinarith [Nat.cast_nonneg rank (α := ℝ)]
  have hrankNat : rank < count := by exact_mod_cast hrank
  have hden : (0 : ℝ) < count - rank := sub_pos.mpr hrank
  have hcast : ((rank * budget / (count - rank) : ℕ) : ℝ) ≤
      (rank : ℝ) * budget / (count - rank) := by
    have := Nat.cast_div_le (α := ℝ) (m := rank * budget) (n := count - rank)
    simpa [Nat.cast_sub hrankNat.le] using this
  apply hcast.trans_lt
  apply (div_lt_div_iff₀ hden (sub_pos.mpr hgamma)).mpr
  have hpositive : (0 : ℝ) < budget := by exact_mod_cast hbudget
  nlinarith

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
