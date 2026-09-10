/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Coordinates

/-!
# The derivative-order partition support

The rate-dependent construction charges `Y_j` by `j`, including the first
derivative. Its monomials satisfy `Σ j b_j ≤ W` and `x + D Σ b_j < L`.
This is a restriction of the existing weighted support, which charges `Y_j` by
`j-1`. Both use the same differential-polynomial representation. The inclusion
allows specialization and executable support-containment proofs to be reused;
the smaller support requires its own dimension and local-rank estimates.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

/-- The rate-partition monomials, with derivative-order weight and a coarse degree cutoff. -/
def RatePartitionEligible (D d W : ℕ) (L : ℝ) (u : JetVariable d →₀ ℕ) : Prop :=
  fullDerivativeJetWeight u ≤ W ∧ (u none + D * totalJetDegree u : ℕ) < L

/-- The new support is contained in the existing higher-jet support. -/
theorem RatePartitionEligible.weightedSupport {D d W : ℕ} {L : ℝ}
    {u : JetVariable d →₀ ℕ} (hu : RatePartitionEligible D d W L u) :
    WeightedSupportEligible D d W L u :=
  ⟨(fullHigherJetWeight_le_fullDerivativeJetWeight u).trans hu.1, hu.2⟩

/-- Finite monomial coordinates for the derivative-order partition support. -/
def ratePartitionExponents (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Finset (JetVariable d →₀ ℕ) :=
  (weightedSupportExponents D d W L hD).filter fun u ↦ fullDerivativeJetWeight u ≤ W

@[simp]
theorem mem_ratePartitionExponents {D d W : ℕ} {L : ℝ} {hD : 0 < D}
    {u : JetVariable d →₀ ℕ} :
    u ∈ ratePartitionExponents D d W L hD ↔ RatePartitionEligible D d W L u := by
  simp only [ratePartitionExponents, Finset.mem_filter, mem_weightedSupportExponents]
  constructor
  · rintro ⟨h, hw⟩
    exact ⟨hw, h.2⟩
  · intro h
    exact ⟨h.weightedSupport, h.1⟩

/-- A positive coarse cutoff always includes the constant monomial, even at rank zero. -/
theorem card_ratePartitionExponents_pos {D d W : ℕ} {L : ℝ}
    (hD : 0 < D) (hL : 0 < L) :
    0 < (ratePartitionExponents D d W L hD).card := by
  apply Finset.card_pos.mpr
  refine ⟨0, mem_ratePartitionExponents.mpr ?_⟩
  simpa [RatePartitionEligible, fullDerivativeJetWeight, totalJetDegree] using
    (show (0 : ℕ) ≤ W ∧ (0 : ℝ) < L from ⟨Nat.zero_le W, hL⟩)

/-- The partition support as a subspace of the existing differential polynomials. -/
def ratePartitionSpace (F : Type*) [CommSemiring F]
    (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(ratePartitionExponents D d W L hD) : Set (JetVariable d →₀ ℕ))

/-- Membership is exactly the two inequalities on every nonzero source coefficient. -/
theorem mem_ratePartitionSpace_iff {F : Type*} [CommSemiring F]
    {D d W : ℕ} {L : ℝ} {hD : 0 < D} {Q : DifferentialPolynomial F d} :
    Q ∈ ratePartitionSpace F D d W L hD ↔
      ∀ u ∈ Q.support, RatePartitionEligible D d W L u := by
  rw [ratePartitionSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_ratePartitionExponents]

/-- The field-generic source dimension equals the exact finite monomial count. -/
theorem finrank_ratePartitionSpace_eq_card {F : Type*} [Field F]
    {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    Module.finrank F (ratePartitionSpace F D d W L hD) =
      (ratePartitionExponents D d W L hD).card := by
  unfold ratePartitionSpace
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport (R := F)
    (↑(ratePartitionExponents D d W L hD) : Set (JetVariable d →₀ ℕ)))]
  exact Fintype.card_coe _

/-- The same strict coarse degree cutoff bounds the new support's total jet degree. -/
theorem totalJetDegree_lt_of_ratePartitionEligible {D d W : ℕ} {L : ℝ}
    (hD : 0 < D) {u : JetVariable d →₀ ℕ} (hu : RatePartitionEligible D d W L u) :
    (totalJetDegree u : ℝ) < L / D :=
  totalJetDegree_lt_of_weightedSupportEligible hD hu.weightedSupport

/-- The rate-partition source reaches the local derivative-order/contact support. -/
theorem ratePartition_localConstraint_support {F : Type*} [CommRing F]
    {D d m W : ℕ} {L : ℝ} {hD : 0 < D}
    (center received : F) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ ratePartitionSpace F D d W L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      Finsupp.weight (localDerivativeJetWeight d) e ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m :=
  localConstraint_support_of_derivative_weight center received
    (fun u hu ↦ (mem_ratePartitionSpace_iff.mp hQ u hu).1) he

end ReedSolomon.HiddenDerivative
