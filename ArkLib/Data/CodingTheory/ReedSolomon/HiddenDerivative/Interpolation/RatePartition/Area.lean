/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Dimension
public import ArkLib.ToMathlib.Combinatorics.QuadraticStaircase

/-!
# A quadratic lower bound for the partition source dimension

Fixing all positive-order derivative exponents leaves two exponents, X and Y₀.
Their exact staircase count dominates the positive-part triangular area.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- A derivative tuple together with an available X,Y₀ coefficient slot. -/
abbrev RatePartitionSlot (D d W : ℕ) (L : ℝ) :=
  Σ b : ↥(weightedHigherJetTuples (d + 1) W),
    QuadraticStaircase.Slot D (L / D - higherJetTupleDegree b.val)

/-- The actual source monomial corresponding to a coefficient slot. -/
def ratePartitionSlotExponent {D d W : ℕ} {L : ℝ}
    (p : RatePartitionSlot D d W L) : JetVariable d →₀ ℕ :=
  ratePartitionSourceExponent p.2.exponents.1 p.2.exponents.2 p.1.val

/-- Every slot belongs to the required support. -/
theorem ratePartitionSlotExponent_eligible {D d W : ℕ} {L : ℝ}
    (hD : 0 < D) (p : RatePartitionSlot D d W L) :
    RatePartitionEligible D d W L (ratePartitionSlotExponent p) := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hslot := QuadraticStaircase.Slot.weighted_degree_lt p.2
  have hcancel : (D : ℝ) * (L / D - higherJetTupleDegree p.1.val) =
      L - D * higherJetTupleDegree p.1.val := by field_simp
  rw [hcancel] at hslot
  refine ⟨?_, ?_⟩
  · simpa [ratePartitionSlotExponent] using mem_weightedHigherJetTuples.mp p.1.2
  · dsimp [ratePartitionSlotExponent]
    simp only [totalJetDegree_ratePartitionSourceExponent,
      Nat.cast_add, Nat.cast_mul]
    linarith

/-- Distinct slots give distinct source monomials. -/
theorem ratePartitionSlotExponent_injective {D d W : ℕ} {L : ℝ} :
    Function.Injective (ratePartitionSlotExponent (D := D) (d := d) (W := W) (L := L)) := by
  rintro ⟨b, p⟩ ⟨c, q⟩ h
  have hb : b = c := by
    apply Subtype.ext
    funext j
    exact congrArg (fun e ↦ e (some j.succ)) h
  subst c
  apply congrArg (Sigma.mk b)
  apply QuadraticStaircase.Slot.exponents_injective
  exact Prod.ext (congrArg (fun e ↦ e none) h) (congrArg (fun e ↦ e (some 0)) h)

/-- The source dimension dominates the sum of all positive-part triangular areas. -/
theorem ratePartition_dimension_ge_quadratic_sum {D d W : ℕ} {L : ℝ}
    (hD : 0 < D) :
    (∑ b ∈ weightedHigherJetTuples (d + 1) W,
      (D : ℝ) * (max (L / D - higherJetTupleDegree b) 0) ^ 2 / 2) ≤
      ((ratePartitionExponents D d W L hD).card : ℝ) := by
  classical
  let f : RatePartitionSlot D d W L → ↥(ratePartitionExponents D d W L hD) :=
    fun p ↦ ⟨ratePartitionSlotExponent p,
      mem_ratePartitionExponents.mpr (ratePartitionSlotExponent_eligible hD p)⟩
  have hf : Function.Injective f := fun p q h ↦
    ratePartitionSlotExponent_injective (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  have hslots : Fintype.card (RatePartitionSlot D d W L) =
      ∑ b ∈ weightedHigherJetTuples (d + 1) W,
        QuadraticStaircase.count D (L / D - higherJetTupleDegree b) := by
    simp only [RatePartitionSlot, Fintype.card_sigma, QuadraticStaircase.card_slot]
    exact Finset.sum_coe_sort (weightedHigherJetTuples (d + 1) W)
      (fun b ↦ QuadraticStaircase.count D (L / D - higherJetTupleDegree b))
  rw [hslots, Fintype.card_coe] at hcard
  calc
    _ ≤ ∑ b ∈ weightedHigherJetTuples (d + 1) W,
        (QuadraticStaircase.count D (L / D - higherJetTupleDegree b) : ℝ) :=
      Finset.sum_le_sum fun b _ ↦ QuadraticStaircase.count_ge_quadratic _ _
    _ ≤ _ := by exact_mod_cast hcard

end ReedSolomon.HiddenDerivative
