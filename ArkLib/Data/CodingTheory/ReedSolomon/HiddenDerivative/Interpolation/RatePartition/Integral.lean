/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Area
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer

/-!
# Transferring the quadratic simplex integral to source coefficients

Flooring coordinates preserves the derivative-weight bound and increases the
remaining X,Y₀ degree budget. Unit cells transfer the whole simplex integral;
no lower cutoff or favorable event is discarded.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory
open scoped BigOperators

/-- Decreasing the ambient slope preserves the rate-envelope triangular lower bound. -/
theorem ratePartition_triangle_rate_lower {D n R L T t : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hR : 0 < R) (ht : 0 ≤ t)
    (hDn : D ≤ R * n) (hL : n * T ≤ L) :
    n / (2 * R) * (max (T - R * t) 0) ^ 2 ≤
      D / 2 * (max (L / D - t) 0) ^ 2 := by
  by_cases hT : 0 < T - R * t
  · rw [max_eq_left hT.le]
    have hbase : n / D * (T - R * t) ≤ L / D - t := by
      have hmul := mul_le_mul_of_nonneg_right hDn ht
      field_simp
      nlinarith
    have hpos : 0 ≤ L / D - t := (by positivity : 0 ≤ n / D * (T - R * t)).trans hbase
    rw [max_eq_left hpos]
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ n / D * (T - R * t)) hbase 2
    have hcoeff : n / (2 * R) ≤ D / 2 * (n / D) ^ 2 := by
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hDn hn.le]
    calc
      _ ≤ (D / 2 * (n / D) ^ 2) * (T - R * t) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = D / 2 * (n / D * (T - R * t)) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  · rw [max_eq_right (le_of_not_gt hT)]
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero]
    positivity

/-- The positive-part quadratic integral is bounded by its finite flooring sum. -/
theorem ratePartition_floor_integral (d W : ℕ) (T : ℝ)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hu : ∀ u ∈ S, ∀ i, 0 ≤ u i)
    (hW : ∀ u ∈ S, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W)
    (hint : IntegrableOn (fun u ↦ (max (T - ∑ i, u i) 0) ^ 2) S volume) :
    (∫ u in S, (max (T - ∑ i, u i) 0) ^ 2) ≤
      ∑ b ∈ weightedHigherJetTuples (d + 1) W,
        (max (T - higherJetTupleDegree b) 0) ^ 2 := by
  classical
  let s := weightedHigherJetTuples (d + 1) W
  let cells := fun b : Fin d → ℕ ↦ S ∩ natFloorCell b
  have hcover : S = ⋃ b ∈ s, cells b := by
    ext u
    constructor
    · intro hus
      have hb := WeightedSupportParameters.floor_higher_mem (d + 1) W u
        (hu u hus) (hW u hus)
      exact Set.mem_iUnion.mpr ⟨fun i ↦ Nat.floor (u i),
        Set.mem_iUnion.mpr ⟨hb, hus,
          (mem_natFloorCell_iff (hu u hus)).mpr (fun _ ↦ rfl)⟩⟩
    · intro h
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
      obtain ⟨_, hh⟩ := Set.mem_iUnion.mp hb
      exact hh.1
  rw [hcover]
  apply integral_biUnion_le_sum_of_cell_measure_le_one s cells
  · exact fun b _ ↦ hS.inter (measurableSet_natFloorCell b)
  · exact fun b _ c _ hbc ↦ Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (disjoint_natFloorCell hbc)
  · exact fun _ _ ↦ hint.mono_set Set.inter_subset_left
  · exact fun b _ ↦ (measure_mono Set.inter_subset_right).trans_eq (volume_natFloorCell b)
  · exact fun _ _ ↦ sq_nonneg _
  · intro b _ u hus
    have heq := (mem_natFloorCell_iff (hu u hus.1)).mp hus.2
    have hf := (sum_natFloor_bounds u (hu u hus.1)).1
    simp_rw [heq] at hf
    have hdegree : (higherJetTupleDegree (d := d + 1) b : ℝ) ≤ ∑ i, u i := by
      simpa [higherJetTupleDegree] using hf
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_max_right _ _)
      (max_le_max_right 0 (sub_le_sub_left hdegree T)) 2

/-- The whole-domain integral gives a lower bound for actual source monomials. -/
theorem ratePartition_dimension_ge_integral {D d W : ℕ} {L : ℝ}
    (hD : 0 < D) (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hu : ∀ u ∈ S, ∀ i, 0 ≤ u i)
    (hW : ∀ u ∈ S, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W)
    (hint : IntegrableOn (fun u ↦ (max (L / D - ∑ i, u i) 0) ^ 2) S volume) :
    (D : ℝ) / 2 * (∫ u in S, (max (L / D - ∑ i, u i) 0) ^ 2) ≤
      ((ratePartitionExponents D d W L hD).card : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (ratePartition_floor_integral d W (L / D) S hS hu hW hint)
    (by positivity : (0 : ℝ) ≤ D / 2)
  apply h.trans
  simpa only [Finset.mul_sum, div_mul_eq_mul_div] using
    ratePartition_dimension_ge_quadratic_sum (d := d) (W := W) (L := L) hD

/-- The rate-envelope source integral uses the actual message length and agreement threshold. -/
theorem ratePartition_dimension_ge_rate_integral {D d W m n A : ℕ} {R a : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hR : 0 < R)
    (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hu : ∀ u ∈ S, ∀ i, 0 ≤ u i)
    (hW : ∀ u ∈ S, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W)
    (hactual : IntegrableOn (fun u ↦
      (max ((m * A : ℕ) / (D : ℝ) - ∑ i, u i) 0) ^ 2) S volume)
    (hrate : IntegrableOn (fun u ↦ (max ((m : ℝ) * a - R * ∑ i, u i) 0) ^ 2)
      S volume) :
    (n : ℝ) / (2 * R) *
      (∫ u in S, (max ((m : ℝ) * a - R * ∑ i, u i) 0) ^ 2) ≤
      ((ratePartitionExponents D d W (m * A : ℕ) hD).card : ℝ) := by
  have hpoint : ∀ u ∈ S,
      (n : ℝ) / (2 * R) * (max ((m : ℝ) * a - R * ∑ i, u i) 0) ^ 2 ≤
      (D : ℝ) / 2 * (max ((m * A : ℕ) / (D : ℝ) - ∑ i, u i) 0) ^ 2 := by
    intro u hus
    apply ratePartition_triangle_rate_lower (by exact_mod_cast hD)
      (by exact_mod_cast hn) hR (Finset.sum_nonneg fun i _ ↦ hu u hus i) hDn
    have h := mul_le_mul_of_nonneg_left haA (Nat.cast_nonneg m (α := ℝ))
    push_cast
    nlinarith only [h]
  have hi := setIntegral_mono_on (hrate.const_mul ((n : ℝ) / (2 * R)))
    (hactual.const_mul ((D : ℝ) / 2)) hS hpoint
  rw [integral_const_mul, integral_const_mul] at hi
  exact hi.trans (ratePartition_dimension_ge_integral hD S hS hu hW hactual)

end ReedSolomon.HiddenDerivative
