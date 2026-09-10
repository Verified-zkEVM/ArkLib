/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.LocalRank

/-!
# The rate-dependent partition support

The derivative budget weights `Y_j` by `j`, for `1 ≤ j ≤ d`; `Y₀` is free.
This differs from the older weighted support, which weights `Y_j` by `j-1`.
Both use the same differential-polynomial representation and coarse specialization cutoff.
The inclusion proved here permits reuse of the existing soundness and executable adapters,
but does not identify their source dimensions or local ranks.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

/-- The derivative-order weight, including weight one for `Y₁`. -/
def fullDerivativeWeight {d : ℕ} (exponent : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun index : Fin (d + 1) ↦ index.val) exponent.some

/-- The new derivative-order weight dominates the old higher-jet weight. -/
theorem fullHigherJetWeight_le_fullDerivativeWeight {d : ℕ}
    (exponent : JetVariable d →₀ ℕ) :
    fullHigherJetWeight exponent ≤ fullDerivativeWeight exponent := by
  unfold fullHigherJetWeight fullDerivativeWeight
  simp only [Finsupp.weight_eq_sum]
  apply Finset.sum_le_sum
  intro index _
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- Finite support with derivative weights `1,...,d` and a strict specialization cutoff. -/
def PartitionSupportEligible (D d W : ℕ) (cutoff : ℝ)
    (exponent : JetVariable d →₀ ℕ) : Prop :=
  fullDerivativeWeight exponent ≤ W ∧
    (exponent none + D * totalJetDegree exponent : ℕ) < cutoff

/-- Inclusion into the legacy support preserves soundness, not its sharper new rank count. -/
theorem PartitionSupportEligible.toWeightedSupportEligible {D d W : ℕ} {cutoff : ℝ}
    {exponent : JetVariable d →₀ ℕ} (heligible : PartitionSupportEligible D d W cutoff exponent) :
    WeightedSupportEligible D d W cutoff exponent :=
  ⟨(fullHigherJetWeight_le_fullDerivativeWeight exponent).trans heligible.1, heligible.2⟩

/-- The coarse degree cutoff gives a finite set of source monomials. -/
theorem partitionSupportEligible_finite {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D) :
    {exponent : JetVariable d →₀ ℕ | PartitionSupportEligible D d W cutoff exponent}.Finite :=
  (weightedSupportEligible_finite hD).subset fun _ heligible ↦
    heligible.toWeightedSupportEligible

/-- The exact monomials counted by the partition construction. -/
def partitionSupportExponents (D d W : ℕ) (cutoff : ℝ) (hD : 0 < D) :
    Finset (JetVariable d →₀ ℕ) :=
  (partitionSupportEligible_finite (d := d) (W := W) (cutoff := cutoff) hD).toFinset

@[simp]
theorem mem_partitionSupportExponents {D d W : ℕ} {cutoff : ℝ} {hD : 0 < D}
    {exponent : JetVariable d →₀ ℕ} :
    exponent ∈ partitionSupportExponents D d W cutoff hD ↔
      PartitionSupportEligible D d W cutoff exponent := by
  simp [partitionSupportExponents]

/-- The new interpolation space, within the existing differential-polynomial type. -/
def partitionSupportSpace (F : Type*) [CommSemiring F] (D d W : ℕ)
    (cutoff : ℝ) (hD : 0 < D) : Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(partitionSupportExponents D d W cutoff hD) : Set (JetVariable d →₀ ℕ))

/-- Membership is precisely the two monomial inequalities. -/
theorem mem_partitionSupportSpace_iff {F : Type*} [CommSemiring F]
    {D d W : ℕ} {cutoff : ℝ} {hD : 0 < D} {equation : DifferentialPolynomial F d} :
    equation ∈ partitionSupportSpace F D d W cutoff hD ↔
      ∀ exponent ∈ equation.support, PartitionSupportEligible D d W cutoff exponent := by
  rw [partitionSupportSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_partitionSupportExponents]

/-- The dimension is the exact number of permitted monomials in every field. -/
theorem finrank_partitionSupportSpace_eq_card {F : Type*} [Field F]
    {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D) :
    Module.finrank F (partitionSupportSpace F D d W cutoff hD) =
      (partitionSupportExponents D d W cutoff hD).card := by
  unfold partitionSupportSpace
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport (R := F)
    (↑(partitionSupportExponents D d W cutoff hD) : Set (JetVariable d →₀ ℕ)))]
  exact Fintype.card_coe _

/-- Every polynomial in the new support retains the old specialization guarantees. -/
theorem partitionSupportSpace_le_weightedSupportSpace {F : Type*} [CommSemiring F]
    {D d W : ℕ} {cutoff : ℝ} (hD : 0 < D) :
    partitionSupportSpace F D d W cutoff hD ≤ weightedSupportSpace F D d W cutoff hD := by
  intro equation hequation
  rw [mem_weightedSupportSpace_iff]
  intro exponent hexponent
  exact (mem_partitionSupportSpace_iff.mp hequation exponent hexponent).toWeightedSupportEligible

end ReedSolomon.HiddenDerivative
