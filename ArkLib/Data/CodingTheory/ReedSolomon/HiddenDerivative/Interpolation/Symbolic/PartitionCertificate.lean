/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.VariableHeight

/-!
# Primitive symbolic certificates on the rate partition support

The finite matrix uses exactly the selected derivative-order-weighted monomials.
Every supported row belongs to the backward-Taylor coordinate count, so its rank is
at most `n * partitionLocalRankBound d m W` over the rational-function field.
The primitive kernel construction then supplies extension-stable nonvanishing and
the exact integer height, without confusing this support with the older free-`Y₁` support.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

/-- Canonical columns for the new derivative-order partition support. -/
def partitionSupportColumns {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D) :
    Fin (Fintype.card ↥(partitionSupportExponents D d W cutoff hD)) → SourceColumn d :=
  fun index ↦ SourceColumn.ofExponent
    (((Fintype.equivFin ↥(partitionSupportExponents D d W cutoff hD)).symm index).1)

@[simp]
theorem partitionSupportColumns_exponent {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D)
    (index : Fin (Fintype.card ↥(partitionSupportExponents D d W cutoff hD))) :
    (partitionSupportColumns hD index).exponent =
      ((Fintype.equivFin ↥(partitionSupportExponents D d W cutoff hD)).symm index).1 := by
  simp [partitionSupportColumns]

/-- Distinct support indices give distinct matrix columns. -/
theorem partitionSupportColumns_injective {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D) :
    Function.Injective (partitionSupportColumns (d := d) (W := W) (cutoff := cutoff) hD) := by
  intro left right hequal
  apply (Fintype.equivFin ↥(partitionSupportExponents D d W cutoff hD)).symm.injective
  apply Subtype.ext
  rw [← partitionSupportColumns_exponent hD left,
    ← partitionSupportColumns_exponent hD right, hequal]

/-- Every canonical column satisfies the new support predicate. -/
theorem partitionSupportColumns_eligible {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D)
    (index : Fin (Fintype.card ↥(partitionSupportExponents D d W cutoff hD))) :
    PartitionSupportEligible D d W cutoff (partitionSupportColumns hD index).exponent := by
  rw [partitionSupportColumns_exponent]
  exact mem_partitionSupportExponents.mp
    ((Fintype.equivFin ↥(partitionSupportExponents D d W cutoff hD)).symm index).2

/-- Actual finite matrix rows fit in the explicit partition rank budget. -/
theorem supportedRows_card_le_partition {F : Type*} [Field F]
    {D d m W n N : ℕ} {cutoff : ℝ} (hD : 0 < D)
    (centers : Fin n → F) (received : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (hcolumns : ∀ index, PartitionSupportEligible D d W cutoff (columns index).exponent) :
    (supportedRows m centers received columns).card ≤ n * partitionLocalRankBound d m W := by
  classical
  let forget : Fin n × LowContactIndex d m → Fin n × (LocalVariable d →₀ ℕ) :=
    fun row ↦ (row.1, row.2.val)
  have hinjective : Function.Injective forget := by
    rintro ⟨left, lrow⟩ ⟨right, rrow⟩ hequal
    have hfirst := congrArg Prod.fst hequal
    have hsecond := congrArg Prod.snd hequal
    exact Prod.ext hfirst (Subtype.ext hsecond)
  have hsubset : (supportedRows m centers received columns).image forget ⊆
      Finset.univ ×ˢ partitionLocalExponents d m W := by
    intro pair hpair
    obtain ⟨row, hrow, rfl⟩ := Finset.mem_image.mp hpair
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [supportedRows, Finset.mem_biUnion] at hrow
    obtain ⟨point, _, index, _, hrow⟩ := hrow
    obtain ⟨contact, hcontact, hequal⟩ := Finset.mem_image.mp hrow
    subst row
    have hmonomial : (columns index).polynomial ∈
        partitionSupportSpace F[X] D d W cutoff hD := by
      rw [mem_partitionSupportSpace_iff]
      intro exponent hexponent
      have heq : exponent = (columns index).exponent := by
        simpa [SourceColumn.polynomial] using MvPolynomial.support_monomial_subset hexponent
      subst exponent
      exact hcolumns index
    have hsupport : contact.val ∈
        (localConstraintAt m (C (centers point)) (received point)
          (columns index).polynomial).support := by
      simpa [lowContactSupport] using hcontact
    obtain ⟨hbalance, hweight, horder⟩ :=
      partitionSupport_localConstraint_support hD _ _ hmonomial hsupport
    exact mem_partitionLocalExponents_of_bounds hbalance hweight horder
  calc
    (supportedRows m centers received columns).card =
        ((supportedRows m centers received columns).image forget).card :=
      (Finset.card_image_of_injective _ hinjective).symm
    _ ≤ (Finset.univ ×ˢ partitionLocalExponents d m W).card := Finset.card_le_card hsubset
    _ = n * (partitionLocalExponents d m W).card := by simp
    _ ≤ n * partitionLocalRankBound d m W :=
      Nat.mul_le_mul_left n (card_partitionLocalExponents_le d m W)

/-- The exact finite support surplus gives a primitive equation with variable jet and height
budgets. All matrix, local-multiplicity, and extension-field conditions are proved here. -/
theorem exists_partition_certificate_of_surplus {F : Type*} [Field F]
    {D d m W n A k ℓ ν : ℕ} {cutoff : ℝ}
    (hD : 0 < D) (hcutoff : cutoff ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    (hkD : k ≤ D + 1) (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ index, (received index).natDegree ≤ ℓ)
    (hdegree : ∀ exponent, PartitionSupportEligible D d W cutoff exponent →
      totalJetDegree exponent ≤ ν)
    (hsurplus : n * partitionLocalRankBound d m W <
      Module.finrank F (partitionSupportSpace F D d W cutoff hD)) :
    let count := Module.finrank F (partitionSupportSpace F D d W cutoff hD)
    let rank := n * partitionLocalRankBound d m W
    Nonempty (Certificate F A k ℓ ν d (rank * (ℓ * ν) / (count - rank)) centers received) := by
  classical
  let columns := partitionSupportColumns (d := d) (W := W) (cutoff := cutoff) hD
  have hinjective := partitionSupportColumns_injective (d := d) (W := W) (cutoff := cutoff) hD
  have heligible := partitionSupportColumns_eligible (d := d) (W := W) (cutoff := cutoff) hD
  have htotal : ∀ index, totalJetDegree (columns index).exponent ≤ ν :=
    fun index ↦ hdegree _ (heligible index)
  have hy₀ : ∀ index, (columns index).y₀ ≤ ν := by
    intro index
    have hcoordinate : (columns index).exponent (some 0) ≤
        totalJetDegree (columns index).exponent :=
      Finsupp.le_degree 0 (columns index).exponent.some
    simp only [SourceColumn.exponent_zero] at hcoordinate
    exact hcoordinate.trans (htotal index)
  have hdimension : Module.finrank F (partitionSupportSpace F D d W cutoff hD) =
      Fintype.card ↥(partitionSupportExponents D d W cutoff hD) := by
    rw [finrank_partitionSupportSpace_eq_card hD, Fintype.card_coe]
  rw [hdimension] at hsurplus ⊢
  have hrank : ((finiteConstraintMatrix m (fun index ↦ centers index) received columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * partitionLocalRankBound d m W := by
    apply (Matrix.rank_le_card_height _).trans
    simp only [Fintype.card_fin, Fintype.card_coe]
    exact supportedRows_card_le_partition hD _ received columns heligible
  obtain ⟨vector, _, hheight, _, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le m ℓ ν (n * partitionLocalRankBound d m W)
      (fun index ↦ centers index) received hreceived columns hinjective hy₀ hrank hsurplus
  refine ⟨⟨interpolant columns vector,
    coeff_interpolant_natDegree_le columns hinjective vector hheight,
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
    hD hcutoff hbudget (fun index ↦ centers index) received columns
    (fun index ↦ (heligible index).toWeightedSupportEligible) vector hconstraints
    embedding challenge indices polynomial hnat centers.injective.injOn hcard hagreement

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
