/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic

/-!
# Partition support acceptance tests

The derivative-order weight charges `Y₁` and the higher-jet weight does not, so at `d = 1`,
`W = 0` the polynomial `Y₁` lies in the weighted support space but not in the partition support
space: the inclusion `partitionSupportSpace_le_weightedSupportSpace` is strict.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The exponent of `Y₁` at `d = 1`: higher-jet weight `0`, derivative-order weight `1`, total jet
degree `1`. -/
private theorem Y_one_weights :
    fullHigherJetWeight (d := 1) (Finsupp.single (some 1) 1) = 0 ∧
      fullDerivativeJetWeight (d := 1) (Finsupp.single (some 1) 1) = 1 ∧
      totalJetDegree (d := 1) (Finsupp.single (some 1) 1) = 1 := by
  simp [fullHigherJetWeight, fullDerivativeJetWeight, totalJetDegree, Finsupp.weight_single,
    jetHigherWeight, jetDerivativeWeight]

/-- At `d = 1`, `D = 1`, `W = 0`, `L = 2`, the polynomial `Y₁` lies in the weighted support space
and not in the partition support space. -/
example : X (some 1) ∈ weightedSupportSpace ℚ 1 1 0 2 one_pos ∧
    X (some 1) ∉ partitionSupportSpace ℚ 1 1 0 2 one_pos := by
  obtain ⟨hw, hd, ht⟩ := Y_one_weights
  refine ⟨mem_weightedSupportSpace_iff.mpr fun u hu => ?_, fun h => ?_⟩
  · rw [X] at hu
    obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hu)
    refine ⟨hw.le, ?_⟩
    simp only [ht]
    norm_num
  · have := (mem_partitionSupportSpace_iff.mp h (Finsupp.single (some 1) 1)
      (by simp [X, support_monomial])).1
    omega
