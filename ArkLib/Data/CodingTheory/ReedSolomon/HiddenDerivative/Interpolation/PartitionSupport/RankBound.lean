/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.CubeTransfer
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.RankBudget

/-!
# Enlarged-simplex bound for the partition rank

The `d` derivative coordinates have weights `1,...,d`. Their disjoint unit
cubes fit in the simplex enlarged by `d*(d+1)/2`; integrating the constant
function gives the lattice bound without any asymptotic error term.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory SimplexIntegration

/-- The weighted partition lattice count is bounded by an enlarged simplex volume. -/
theorem partition_count_le_volume (d budget : ℕ) :
    (weightedHigherJetCount (d + 1) budget : ℝ) ≤
      ((budget : ℝ) + ((d + 1).choose 2 : ℝ)) ^ d / (d.factorial : ℝ) ^ 2 := by
  have hweights : (∑ index : Fin d, coordinateWeight index) =
      ((d + 1).choose 2 : ℝ) := coordinateWeight_sum (d + 1)
  have hradius : 0 ≤ (budget : ℝ) + ∑ index : Fin d, coordinateWeight index := by
    rw [hweights]
    positivity
  have hsum := sum_le_integral_of_unit_cells
    (weightedHigherJetTuples (d + 1) budget) natFloorCell
    (weightedSimplex d ((budget : ℝ) + ∑ index : Fin d, coordinateWeight index))
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun jets _ ↦ measurableSet_natFloorCell jets)
    (fun _ _ _ _ hne ↦ disjoint_natFloorCell hne)
    (fun jets _ ↦ volume_natFloorCell jets)
    (fun _ hmem ↦ floorCell_subset_weightedSimplex hmem)
    (Continuous.integrableOn_weightedSimplex continuous_const hradius)
    (fun _ ↦ zero_le_one) (fun _ _ _ _ ↦ le_rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, integral_const, smul_eq_mul] at hsum
  simp only [Measure.real, Measure.restrict_apply_univ] at hsum
  change ((weightedHigherJetTuples (d + 1) budget).card : ℝ) ≤
    volume.real (weightedSimplex d ((budget : ℝ) + ∑ index : Fin d, coordinateWeight index)) at hsum
  rw [volume_weightedSimplex d hradius, hweights] at hsum
  simpa [weightedHigherJetCount] using hsum

/-- The contact ceiling retains its full denominator, including the extra error slot. -/
theorem partition_ceilDiv_le (slots count : ℕ) (hslots : 0 < slots) :
    ((count ⌈/⌉ slots : ℕ) : ℝ) ≤ (count : ℝ) / slots + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  apply (Nat.cast_div_le (m := count + slots - 1) (n := slots)).trans
  have hpred : ((count + slots - 1 : ℕ) : ℝ) ≤ (count : ℝ) + slots := by
    exact_mod_cast Nat.sub_le (count + slots) 1
  have hslotsReal : (0 : ℝ) < slots := by exact_mod_cast hslots
  calc
    _ ≤ ((count : ℝ) + slots) / slots :=
      div_le_div_of_nonneg_right hpred hslotsReal.le
    _ = _ := by rw [add_div, div_self hslotsReal.ne']

/-- Exact contact denominator in the finite exponential tail. -/
theorem partition_contact_exp_sum_le (slots multiplicity : ℕ) (hslots : 0 < slots)
    {exponent offset : ℝ} (hexponent : 0 < exponent) :
    (∑ residual ∈ Finset.range multiplicity,
      (((multiplicity - residual) ⌈/⌉ slots : ℕ) : ℝ) *
        Real.exp (exponent * (residual + offset))) ≤
      Real.exp (exponent * (multiplicity + offset)) *
        (1 / ((slots : ℝ) * exponent ^ 2) + 1 / exponent) := by
  rw [← Finset.sum_range_reflect
    (fun residual ↦ (((multiplicity - residual) ⌈/⌉ slots : ℕ) : ℝ) *
      Real.exp (exponent * (residual + offset))) multiplicity]
  have hterm : ∀ index ∈ Finset.range multiplicity,
      (((multiplicity - (multiplicity - 1 - index)) ⌈/⌉ slots : ℕ) : ℝ) *
          Real.exp (exponent * ((multiplicity - 1 - index : ℕ) + offset)) ≤
        Real.exp (exponent * (multiplicity + offset)) *
          ((((index + 1 : ℕ) : ℝ) / slots + 1) * Real.exp (-exponent) ^ (index + 1)) := by
    intro index hindex
    have hindexLt := Finset.mem_range.mp hindex
    have heq : multiplicity - (multiplicity - 1 - index) = index + 1 := by omega
    have hadd : multiplicity - 1 - index + (index + 1) = multiplicity := by omega
    have hcast : ((multiplicity - 1 - index : ℕ) : ℝ) + (index + 1 : ℕ) = multiplicity := by
      exact_mod_cast hadd
    have hexp : Real.exp (exponent * ((multiplicity - 1 - index : ℕ) + offset)) =
        Real.exp (exponent * (multiplicity + offset)) * Real.exp (-exponent) ^ (index + 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast at hcast ⊢
      nlinarith
    rw [heq, hexp]
    have hbound := mul_le_mul_of_nonneg_right (partition_ceilDiv_le slots (index + 1) hslots)
      (by positivity : 0 ≤ Real.exp (exponent * (multiplicity + offset)) *
        Real.exp (-exponent) ^ (index + 1))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (localRank_linear_exp_sum_le slots multiplicity hslots hexponent) (Real.exp_pos _).le)

/-- The partition rank bound with all floor and ceiling errors retained. -/
theorem partitionLocalRankBound_le_geometric (d multiplicity budget : ℕ)
    (hd : 0 < d) (hbudget : 0 < budget) :
    (partitionLocalRankBound d multiplicity budget : ℝ) ≤
      ((budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / budget) * (multiplicity + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / budget) ^ 2) + 1 / ((d : ℝ) / budget)) := by
  let exponent : ℝ := (d : ℝ) / budget
  let volumeFactor : ℝ := (budget : ℝ) ^ d / (d.factorial : ℝ) ^ 2
  have hexponent : 0 < exponent := div_pos (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr hbudget)
  have hvolume : 0 ≤ volumeFactor := by positivity
  have hfiber : ∀ residual : ℕ,
      (weightedHigherJetCount (d + 1) (budget + residual) : ℝ) ≤
        volumeFactor * Real.exp (exponent * (residual + (d + 1).choose 2)) := by
    intro residual
    simpa [volumeFactor, exponent] using
      localRank_weightedHigherJetCount_le_exp (d + 1) budget residual hbudget
  have hsum : (partitionLocalRankBound d multiplicity budget : ℝ) ≤
      volumeFactor * ∑ residual ∈ Finset.range multiplicity,
        (((multiplicity - residual) ⌈/⌉ (d + 1) : ℕ) : ℝ) *
          Real.exp (exponent * (residual + (d + 1).choose 2)) := by
    unfold partitionLocalRankBound
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro residual _
    have hbound := mul_le_mul_of_nonneg_left (hfiber residual)
      (Nat.cast_nonneg ((multiplicity - residual) ⌈/⌉ (d + 1)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound
  have htail := partition_contact_exp_sum_le (d + 1) multiplicity (by omega)
    (offset := ((d + 1).choose 2 : ℝ)) hexponent
  exact hsum.trans (by
    simpa [volumeFactor, exponent, mul_assoc] using mul_le_mul_of_nonneg_left htail hvolume)

end ReedSolomon.HiddenDerivative
