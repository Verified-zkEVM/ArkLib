/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Basic

/-!
# Exact source count for the derivative-order partition support

Fix a derivative tuple b of weight at most W and a Y₀ exponent u. The remaining
X exponents number `(L-D*(u+|b|))₊`. Summing these fibers gives the exact source
dimension. The finite outer cutoff on u is redundant for every nonempty fiber
when D is positive, so this is also the infinite-sum formula in the paper.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- A source exponent from its X, Y₀, and derivative coordinates. -/
def ratePartitionSourceExponent {d : ℕ} (x u : ℕ) (b : Fin d → ℕ) :
    JetVariable d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v ↦ match v with
    | none => x
    | some j => Fin.cases u b j

@[simp]
theorem ratePartitionSourceExponent_none {d : ℕ} (x u : ℕ) (b : Fin d → ℕ) :
    ratePartitionSourceExponent x u b none = x := rfl

@[simp]
theorem totalJetDegree_ratePartitionSourceExponent {d : ℕ} (x u : ℕ) (b : Fin d → ℕ) :
    totalJetDegree (ratePartitionSourceExponent x u b) =
      u + higherJetTupleDegree (d := d + 1) b := by
  simp [totalJetDegree, Finsupp.degree_eq_sum, ratePartitionSourceExponent,
    Fin.sum_univ_succ, higherJetTupleDegree]

@[simp]
theorem fullDerivativeJetWeight_ratePartitionSourceExponent {d : ℕ}
    (x u : ℕ) (b : Fin d → ℕ) :
    fullDerivativeJetWeight (ratePartitionSourceExponent x u b) =
      higherJetTupleWeight (d := d + 1) b := by
  simp [fullDerivativeJetWeight, Finsupp.weight_eq_sum, ratePartitionSourceExponent,
    Fin.sum_univ_succ, higherJetTupleWeight, Nat.mul_comm]

/-- Recover every full source exponent from these coordinates. -/
theorem ratePartitionSourceExponent_coordinates {d : ℕ} (e : JetVariable d →₀ ℕ) :
    ratePartitionSourceExponent (e none) (e (some 0)) (fun j ↦ e (some j.succ)) = e := by
  ext v
  rcases v with _ | j
  · rfl
  · induction j using Fin.cases <;> rfl

/-- Finite dependent index for all eligible source monomials at integer cutoff L. -/
abbrev RatePartitionDimensionIndex (D d W L : ℕ) :=
  Σ b : ↥(weightedHigherJetTuples (d + 1) W),
    Σ u : Fin (L + 1), Fin (L - D * (u.val + higherJetTupleDegree b.val))

/-- The exact finite source count, using natural subtraction for the positive part. -/
def ratePartitionDimensionCount (D d W L : ℕ) : ℕ :=
  ∑ b ∈ weightedHigherJetTuples (d + 1) W,
    ∑ u ∈ Finset.range (L + 1), (L - D * (u + higherJetTupleDegree b))

/-- Counting the dependent fibers yields the displayed double sum. -/
theorem card_ratePartitionDimensionIndex (D d W L : ℕ) :
    Fintype.card (RatePartitionDimensionIndex D d W L) =
      ratePartitionDimensionCount D d W L := by
  simp only [RatePartitionDimensionIndex, Fintype.card_sigma, Fintype.card_fin,
    ratePartitionDimensionCount]
  rw [Finset.sum_coe_sort (weightedHigherJetTuples (d + 1) W)
    (fun b ↦ ∑ u : Fin (L + 1), (L - D * (u.val + higherJetTupleDegree b)))]
  apply Finset.sum_congr rfl
  intro b _
  exact Fin.sum_univ_eq_sum_range
    (fun u ↦ L - D * (u + higherJetTupleDegree b)) (L + 1)

/-- Interpret a finite dimension index as a full source exponent. -/
def ratePartitionDimensionExponent {D d W L : ℕ} (p : RatePartitionDimensionIndex D d W L) :
    JetVariable d →₀ ℕ :=
  ratePartitionSourceExponent p.2.2.val p.2.1.val p.1.val

/-- Distinct dimension indices represent distinct source monomials. -/
theorem ratePartitionDimensionExponent_injective {D d W L : ℕ} :
    Function.Injective (ratePartitionDimensionExponent (D := D) (d := d) (W := W) (L := L)) := by
  intro p q hpq
  have hb : p.1 = q.1 := by
    apply Subtype.ext
    funext j
    exact congrArg (fun e ↦ e (some j.succ)) hpq
  cases p with | mk pb pu =>
    cases q with | mk qb qu =>
      dsimp only at hb
      subst qb
      congr 1
      have hu : pu.1 = qu.1 := by
        apply Fin.ext
        exact congrArg (fun e ↦ e (some 0)) hpq
      cases pu with | mk u x =>
        cases qu with | mk v y =>
          dsimp only at hu
          subst v
          congr 1
          apply Fin.ext
          exact congrArg (fun e ↦ e none) hpq

/-- Each finite dimension index satisfies the derivative and coarse degree restrictions. -/
theorem ratePartitionDimensionExponent_eligible {D d W L : ℕ}
    (p : RatePartitionDimensionIndex D d W L) :
    RatePartitionEligible D d W (L : ℝ) (ratePartitionDimensionExponent p) := by
  refine ⟨?_, ?_⟩
  · simpa [ratePartitionDimensionExponent] using mem_weightedHigherJetTuples.mp p.1.2
  · have hx := Nat.lt_sub_iff_add_lt.mp p.2.2.isLt
    dsimp [ratePartitionDimensionExponent]
    simp only [totalJetDegree_ratePartitionSourceExponent]
    exact_mod_cast hx

/-- Every eligible source monomial occurs in the finite fiber enumeration. -/
theorem exists_ratePartitionDimensionExponent {D d W L : ℕ} (hD : 0 < D)
    {e : JetVariable d →₀ ℕ} (he : RatePartitionEligible D d W (L : ℝ) e) :
    ∃ p : RatePartitionDimensionIndex D d W L, ratePartitionDimensionExponent p = e := by
  let b : Fin d → ℕ := fun j ↦ e (some j.succ)
  have hrepr := ratePartitionSourceExponent_coordinates e
  have ht : totalJetDegree e = e (some 0) + higherJetTupleDegree (d := d + 1) b := by
    simpa only [totalJetDegree_ratePartitionSourceExponent] using
      (congrArg totalJetDegree hrepr).symm
  have hweight : fullDerivativeJetWeight e = higherJetTupleWeight (d := d + 1) b := by
    simpa only [fullDerivativeJetWeight_ratePartitionSourceExponent] using
      (congrArg fullDerivativeJetWeight hrepr).symm
  have hw : b ∈ weightedHigherJetTuples (d + 1) W := by
    apply mem_weightedHigherJetTuples.mpr
    rw [← hweight]
    exact he.1
  have hcost : e none + D * (e (some 0) + higherJetTupleDegree (d := d + 1) b) < L := by
    have hc := he.2
    rw [ht] at hc
    exact_mod_cast hc
  have hu : e (some 0) < L + 1 := by
    have hm := Nat.mul_le_mul_right (e (some 0) + higherJetTupleDegree (d := d + 1) b) hD
    omega
  refine ⟨⟨⟨b, hw⟩, ⟨⟨e (some 0), hu⟩,
    ⟨e none, Nat.lt_sub_iff_add_lt.mpr hcost⟩⟩⟩, ?_⟩
  exact hrepr

/-- The exact support cardinality equals the finite dimension formula. -/
theorem card_ratePartitionExponents_eq_dimensionCount {D d W L : ℕ} (hD : 0 < D) :
    (ratePartitionExponents D d W (L : ℝ) hD).card =
      ratePartitionDimensionCount D d W L := by
  classical
  have heq : ratePartitionExponents D d W (L : ℝ) hD =
      Finset.univ.image (ratePartitionDimensionExponent (D := D) (d := d) (W := W) (L := L)) := by
    ext e
    simp only [mem_ratePartitionExponents, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨exists_ratePartitionDimensionExponent hD, fun ⟨p, hp⟩ ↦ hp ▸
      ratePartitionDimensionExponent_eligible p⟩
  rw [heq, Finset.card_image_of_injective _ ratePartitionDimensionExponent_injective,
    Finset.card_univ, card_ratePartitionDimensionIndex]

end ReedSolomon.HiddenDerivative
