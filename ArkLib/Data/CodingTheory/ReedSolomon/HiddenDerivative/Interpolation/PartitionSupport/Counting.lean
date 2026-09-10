/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.Basic

/-!
# Finite source count for the partition support

After choosing the derivative tuple `b` and the `Y₀` exponent `u`, there are
`(m*A-D*(u+Σ b))_+` choices of the `X` exponent. The finite sum uses `u<m*A`;
all terms beyond that range vanish when `D>0`.
The explicit index below injects into the actual monomial basis, furnishing the
source lower bound used by the simplex integral comparison.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- The executable source count, with natural subtraction representing the positive part. -/
def partitionSourceCount (D d m A W : ℕ) : ℕ :=
  ∑ jets ∈ weightedHigherJetTuples (d + 1) W,
    ∑ zeroth ∈ Finset.range (m * A), (m * A - D * (zeroth + ∑ index, jets index))

/-- One source monomial for each derivative tuple, zeroth jet, and residual `X` exponent. -/
abbrev PartitionSourceIndex (D d m A W : ℕ) :=
  Σ jets : ↥(weightedHigherJetTuples (d + 1) W),
    Σ zeroth : Fin (m * A), Fin (m * A - D * (zeroth.val + ∑ index, jets.val index))

/-- The dependent source index has exactly the finite source-sum cardinality. -/
theorem card_partitionSourceIndex (D d m A W : ℕ) :
    Fintype.card (PartitionSourceIndex D d m A W) = partitionSourceCount D d m A W := by
  simp only [PartitionSourceIndex, Fintype.card_sigma, Fintype.card_fin, partitionSourceCount]
  rw [Finset.sum_coe_sort (weightedHigherJetTuples (d + 1) W)
    (fun jets ↦ ∑ zeroth : Fin (m * A), (m * A - D * (zeroth.val + ∑ index, jets index)))]
  apply Finset.sum_congr rfl
  intro jets _
  exact Fin.sum_univ_eq_sum_range
    (fun zeroth ↦ m * A - D * (zeroth + ∑ index, jets index)) (m * A)

/-- Assemble the differential monomial from the finite source index. -/
def partitionSourceExponent {D d m A W : ℕ} (source : PartitionSourceIndex D d m A W) :
    JetVariable d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun slot ↦
    match slot with
    | none => source.2.2.val
    | some index => Fin.cases source.2.1.val source.1.val index

@[simp]
theorem partitionSourceExponent_none {D d m A W : ℕ}
    (source : PartitionSourceIndex D d m A W) :
    partitionSourceExponent source none = source.2.2.val := rfl

@[simp]
theorem partitionSourceExponent_zero {D d m A W : ℕ}
    (source : PartitionSourceIndex D d m A W) :
    partitionSourceExponent source (some 0) = source.2.1.val := rfl

@[simp]
theorem partitionSourceExponent_succ {D d m A W : ℕ}
    (source : PartitionSourceIndex D d m A W) (index : Fin d) :
    partitionSourceExponent source (some index.succ) = source.1.val index := rfl

/-- The monomial's derivative-order weight is exactly its tuple weight. -/
theorem fullDerivativeWeight_partitionSourceExponent {D d m A W : ℕ}
    (source : PartitionSourceIndex D d m A W) :
    fullDerivativeWeight (partitionSourceExponent source) = higherJetTupleWeight source.1.val := by
  simp only [fullDerivativeWeight, Finsupp.weight_eq_sum, Finsupp.some_apply, nsmul_eq_mul]
  rw [Fin.sum_univ_succ]
  simp [higherJetTupleWeight, mul_comm]

/-- The total jet degree is the zeroth exponent plus the ordinary tuple degree. -/
theorem totalJetDegree_partitionSourceExponent {D d m A W : ℕ}
    (source : PartitionSourceIndex D d m A W) :
    totalJetDegree (partitionSourceExponent source) =
      source.2.1.val + ∑ index, source.1.val index := by
  simp only [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.some_apply]
  rw [Fin.sum_univ_succ]
  simp

/-- Every index gives an actual eligible monomial, including the strict cutoff boundary. -/
theorem partitionSourceExponent_eligible {D d m A W : ℕ}
    (source : PartitionSourceIndex D d m A W) :
    PartitionSupportEligible D d W (m * A : ℕ) (partitionSourceExponent source) := by
  refine ⟨?_, ?_⟩
  · rw [fullDerivativeWeight_partitionSourceExponent]
    exact mem_weightedHigherJetTuples.mp source.1.property
  · rw [partitionSourceExponent_none, totalJetDegree_partitionSourceExponent]
    exact_mod_cast Nat.lt_sub_iff_add_lt.mp source.2.2.isLt

/-- The finite source coordinates can be recovered from the monomial. -/
theorem partitionSourceExponent_injective {D d m A W : ℕ} :
    Function.Injective (partitionSourceExponent (D := D) (d := d) (m := m) (A := A) (W := W)) := by
  rintro ⟨leftJets, leftZero, leftX⟩ ⟨rightJets, rightZero, rightX⟩ hequal
  have hjets : leftJets = rightJets := by
    apply Subtype.ext
    funext index
    exact congrArg (fun exponent ↦ exponent (some index.succ)) hequal
  subst rightJets
  have hzero : leftZero = rightZero := by
    apply Fin.ext
    exact congrArg (fun exponent ↦ exponent (some 0)) hequal
  subst rightZero
  have hx : leftX = rightX := by
    apply Fin.ext
    exact congrArg (fun exponent ↦ exponent none) hequal
  subst rightX
  rfl

/-- The actual interpolation dimension contains the entire explicitly counted source family. -/
theorem partitionSourceCount_le_finrank {F : Type*} [Field F]
    {D d m A W : ℕ} (hD : 0 < D) :
    partitionSourceCount D d m A W ≤
      Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) := by
  rw [finrank_partitionSupportSpace_eq_card hD, ← card_partitionSourceIndex,
    ← Fintype.card_coe]
  apply Fintype.card_le_of_injective
    (fun source ↦ (⟨partitionSourceExponent source,
      mem_partitionSupportExponents.mpr (partitionSourceExponent_eligible source)⟩ :
        ↥(partitionSupportExponents D d W (m * A : ℕ) hD)))
  intro left right hequal
  exact partitionSourceExponent_injective (congrArg Subtype.val hequal)

/-- Split the derivative-order weight into the `d` positively weighted coordinates. -/
theorem fullDerivativeWeight_eq_sum_succ {d : ℕ} (exponent : JetVariable d →₀ ℕ) :
    fullDerivativeWeight exponent =
      ∑ index : Fin d, (index.val + 1) * exponent (some index.succ) := by
  simp only [fullDerivativeWeight, Finsupp.weight_eq_sum, Finsupp.some_apply, nsmul_eq_mul]
  rw [Fin.sum_univ_succ]
  simp [mul_comm]

/-- Split total jet degree into the zeroth jet and the positively weighted coordinates. -/
theorem totalJetDegree_eq_zero_add_sum_succ {d : ℕ} (exponent : JetVariable d →₀ ℕ) :
    totalJetDegree exponent = exponent (some 0) +
      ∑ index : Fin d, exponent (some index.succ) := by
  simp only [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.some_apply]
  exact Fin.sum_univ_succ _

/-- Every eligible monomial has an index in the finite source sum; omitted zeroth-jet
exponents cannot satisfy the strict specialization cutoff. -/
theorem partitionSourceExponent_covers {D d m A W : ℕ} (hD : 0 < D)
    {exponent : JetVariable d →₀ ℕ}
    (heligible : PartitionSupportEligible D d W (m * A : ℕ) exponent) :
    ∃ source : PartitionSourceIndex D d m A W, partitionSourceExponent source = exponent := by
  have hjets : (fun index : Fin d ↦ exponent (some index.succ)) ∈
      weightedHigherJetTuples (d + 1) W := by
    apply mem_weightedHigherJetTuples.mpr
    simpa [fullDerivativeWeight_eq_sum_succ, higherJetTupleWeight] using heligible.1
  have hcost : exponent none + D * totalJetDegree exponent < m * A := by
    exact_mod_cast heligible.2
  have hcoordinate : exponent (some 0) ≤ totalJetDegree exponent :=
    Finsupp.le_degree 0 exponent.some
  have hzero : exponent (some 0) < m * A := by nlinarith
  rw [totalJetDegree_eq_zero_add_sum_succ] at hcost
  let source : PartitionSourceIndex D d m A W :=
    ⟨⟨_, hjets⟩, ⟨exponent (some 0), hzero⟩,
      ⟨exponent none, Nat.lt_sub_iff_add_lt.mpr hcost⟩⟩
  refine ⟨source, ?_⟩
  ext slot
  rcases slot with _ | index
  · rfl
  · induction index using Fin.cases with
    | zero => rfl
    | succ index => rfl

/-- The source sum equals the actual interpolation dimension, not just a lower estimate. -/
theorem finrank_partitionSupportSpace_eq_sourceCount {F : Type*} [Field F]
    {D d m A W : ℕ} (hD : 0 < D) :
    Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) =
      partitionSourceCount D d m A W := by
  rw [finrank_partitionSupportSpace_eq_card hD, ← card_partitionSourceIndex,
    ← Fintype.card_coe]
  let encode : PartitionSourceIndex D d m A W →
      ↥(partitionSupportExponents D d W (m * A : ℕ) hD) := fun source ↦
    ⟨partitionSourceExponent source,
      mem_partitionSupportExponents.mpr (partitionSourceExponent_eligible source)⟩
  have hinjective : Function.Injective encode := by
    intro left right hequal
    exact partitionSourceExponent_injective (congrArg Subtype.val hequal)
  have hsurjective : Function.Surjective encode := by
    intro exponent
    obtain ⟨source, hsource⟩ := partitionSourceExponent_covers hD
      (mem_partitionSupportExponents.mp exponent.property)
    exact ⟨source, Subtype.ext hsource⟩
  exact (Fintype.card_of_bijective ⟨hinjective, hsurjective⟩).symm

end ReedSolomon.HiddenDerivative
