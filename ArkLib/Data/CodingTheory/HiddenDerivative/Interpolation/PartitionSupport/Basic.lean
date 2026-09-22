/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic
public import ArkLib.Data.MvPolynomial.WeightAtMost

/-!
# The derivative-order partition support

An exponent `u` of `X^a Y₀^(b₀) ⋯ Y_d^(b_d)` is *partition-support eligible* for parameters `D`,
`W` and a real cutoff `L` when its derivative-order weight `∑_j j b_j` is at most `W` and its coarse
specialization weight `a + D · ∑_j b_j` is strictly below `L`. The derivative-order weight gives
`Y_j` weight `j` for `1 ≤ j ≤ d`, so it charges `Y₁`, while the higher-jet weight of the weighted
support gives `Y_j` weight `j - 1`; `Y₀` is free in both. Both use the same coarse cutoff.

Since `j - 1 ≤ j`, partition-support eligibility implies weighted-support eligibility, so the
partition support space lies in the weighted support space and inherits its finiteness and
decoder degree bounds. The inclusion does not compare dimensions or local ranks: the local rank of
the partition support is counted separately in `PartitionSupport/LocalRank.lean`.

## Main statements

* `PartitionSupportEligible`, `PartitionSupportEligible.toWeightedSupportEligible`,
  `partitionSupportEligible_finite`, `partitionSupportExponents`.
* `partitionSupportSpace`, `mem_partitionSupportSpace_iff`,
  `finrank_partitionSupportSpace_eq_card`, `partitionSupportSpace_le_weightedSupportSpace`.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/PartitionSupport/Basic.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* The source's `fullDerivativeWeight` is the existing `fullDerivativeJetWeight` of
  `Interpolation/Space.lean`, and its `fullHigherJetWeight_le_fullDerivativeWeight` is the existing
  `fullHigherJetWeight_le_fullDerivativeJetWeight`; neither is restated.
* `PartitionSupportEligible`, `PartitionSupportEligible.toWeightedSupportEligible`,
  `partitionSupportEligible_finite`, `partitionSupportExponents`,
  `mem_partitionSupportExponents`, `mem_partitionSupportSpace_iff`,
  `finrank_partitionSupportSpace_eq_card` and `partitionSupportSpace_le_weightedSupportSpace` keep
  their statements.
* The source imports `WeightedSupport/LocalRank.lean`; this file needs only
  `WeightedSupport/Basic.lean`.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} {d D W : ℕ} {L : ℝ}

/-- An exponent is partition-support eligible when its derivative-order weight `∑_j j b_j` is at
most `W` and its coarse specialization weight `a + D · ∑_j b_j` is strictly below `L`. -/
def PartitionSupportEligible (D d W : ℕ) (L : ℝ) (u : JetVariable d →₀ ℕ) : Prop :=
  fullDerivativeJetWeight u ≤ W ∧ (u none + D * totalJetDegree u : ℕ) < L

/-- Partition-support eligibility implies weighted-support eligibility with the same parameters,
since the higher-jet weight is at most the derivative-order weight. -/
theorem PartitionSupportEligible.toWeightedSupportEligible {u : JetVariable d →₀ ℕ}
    (hu : PartitionSupportEligible D d W L u) : WeightedSupportEligible D d W L u :=
  ⟨(fullHigherJetWeight_le_fullDerivativeJetWeight u).trans hu.1, hu.2⟩

/-- For `0 < D` there are finitely many partition-support eligible exponents. For `D = 0` and
`0 < L` every power of `Y₀` is eligible. -/
theorem partitionSupportEligible_finite (hD : 0 < D) :
    {u : JetVariable d →₀ ℕ | PartitionSupportEligible D d W L u}.Finite :=
  (weightedSupportEligible_finite (W := W) (L := L) hD).subset fun _ hu =>
    PartitionSupportEligible.toWeightedSupportEligible hu

/-- The finite set of partition-support eligible exponents, for `0 < D`. -/
def partitionSupportExponents (D d W : ℕ) (L : ℝ) (hD : 0 < D) : Finset (JetVariable d →₀ ℕ) :=
  (partitionSupportEligible_finite (d := d) (W := W) (L := L) hD).toFinset

@[simp]
theorem mem_partitionSupportExponents {hD : 0 < D} {u : JetVariable d →₀ ℕ} :
    u ∈ partitionSupportExponents D d W L hD ↔ PartitionSupportEligible D d W L u := by
  simp [partitionSupportExponents]

/-- The partition support space: differential polynomials whose support consists of
partition-support eligible exponents. -/
def partitionSupportSpace (F : Type*) [CommSemiring F] (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(partitionSupportExponents D d W L hD) : Set (JetVariable d →₀ ℕ))

/-- A polynomial lies in the partition support space exactly when every exponent of its support is
eligible. -/
theorem mem_partitionSupportSpace_iff [CommSemiring F] {hD : 0 < D}
    {Q : DifferentialPolynomial F d} :
    Q ∈ partitionSupportSpace F D d W L hD ↔
      ∀ u ∈ Q.support, PartitionSupportEligible D d W L u := by
  rw [partitionSupportSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_partitionSupportExponents]

/-- The dimension of the partition support space over a field is the number of eligible
exponents. -/
theorem finrank_partitionSupportSpace_eq_card [Field F] (hD : 0 < D) :
    Module.finrank F (partitionSupportSpace F D d W L hD) =
      (partitionSupportExponents D d W L hD).card := by
  rw [partitionSupportSpace, MvPolynomial.finrank_restrictSupport_finset]

/-- The partition support space lies in the weighted support space with the same parameters. -/
theorem partitionSupportSpace_le_weightedSupportSpace [CommSemiring F] (hD : 0 < D) :
    partitionSupportSpace F D d W L hD ≤ weightedSupportSpace F D d W L hD := fun _ hQ =>
  mem_weightedSupportSpace_iff.mpr fun u hu =>
    (mem_partitionSupportSpace_iff.mp hQ u hu).toWeightedSupportEligible

end ReedSolomon.HiddenDerivative
