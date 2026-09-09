/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge
/-!
# Canaries for the exact interpolation dimension bridge

The main canary shows that `0 < d` cannot be erased from the bridge.  At derivative order zero,
the proof-facing interpolation support has no `Y₁` coordinate, whereas the nested dimension
count still ranges over a formal `b₁`.  A concrete parameter tuple therefore gives cardinalities
one and two.
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

/-- At `d = 0` and unit weight budget, the exact interpolation support contains only zero. -/
theorem exactInterpolationExponents_d_zero_eq_singleton :
    exactInterpolationExponents 1 1 0 1 1 0 (by omega) = {0} := by
  ext u
  rw [mem_exactInterpolationExponents, Finset.mem_singleton]
  constructor
  · intro hu
    apply Finsupp.ext
    intro v
    cases v with
    | none => simpa using xExponent_le_pred_of_exact_eligible hu
    | some j =>
      have ht := totalJetDegree_le_floor_of_exact_eligible (by omega) hu
      have hj := Finsupp.le_degree j u.some
      have hz : totalJetDegree u = 0 := by
        simpa [exactInterpolationJetDegreeFloor] using ht
      have hz' : Finsupp.degree u.some = 0 := hz
      exact Nat.le_zero.mp (hj.trans_eq hz')
  · rintro rfl
    simp [ExactInterpolationEligibleExponent, exactInterpolationMonomialWeight,
      firstJetExponent, fullHigherJetWeight, Finsupp.weight_apply]

/-- At the same `d = 0` tuple, the nested formula counts a phantom `b₁` choice. -/
theorem exactInterpolationDimensionCount_d_zero_eq_two :
    exactInterpolationDimensionCount 1 1 0 1 1 0 = 2 := by
  decide

/-- Concrete cardinality mismatch proving that the bridge must assume `0 < d`. -/
theorem exactInterpolation_card_ne_dimensionCount_at_d_zero :
    (exactInterpolationExponents 1 1 0 1 1 0 (by omega)).card ≠
      exactInterpolationDimensionCount 1 1 0 1 1 0 := by
  rw [exactInterpolationExponents_d_zero_eq_singleton,
    exactInterpolationDimensionCount_d_zero_eq_two]
  decide

/-- A positive-order instantiation exercises the public cardinality bridge. -/
theorem exactInterpolation_card_eq_dimensionCount_small_canary :
    (exactInterpolationExponents 4 3 2 2 2 3 (by omega)).card =
      exactInterpolationDimensionCount 4 3 2 2 2 3 :=
  card_exactInterpolationExponents_eq_exactInterpolationDimensionCount (by omega) (by omega)

end
end HiddenDerivative
end ReedSolomon
