/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank

/-!
# Symbolic local rank acceptance tests

* At `d = 1`, `D = 1`, `W = 0`, `L = 2` the polynomial `X` lies in the weighted support space,
  and the translation automorphism sends it to `C c + X`.
* At `L = 1` the constant exponent `0` is a column, and the entry of the coordinate matrix at
  this column and the row `0` is `1` at every point.
* For `m = 0` there are no rows and the coordinate matrix has rank `0` at every point.
* The source shapes `weightedSupportLocalCoordinateMatrix_zero_baseChange` (derived from
  `weightedSupportLocalCoordinateMatrix_map`) and the extension-field bound over an arbitrary
  point.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- `X` is eligible at `D = 1`, `W = 0`, `L = 2`: its coarse weight is `1 < 2`. -/
theorem X_mem_weightedSupportSpace_test :
    (X none : DifferentialPolynomial ℚ 1) ∈
      weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos := by
  rw [mem_weightedSupportSpace_iff, support_X]
  intro u hu
  obtain rfl := Finset.mem_singleton.mp hu
  simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree, Finsupp.weight_single,
    jetHigherWeight, jetDegreeWeight]

/-- Translation by `(c, r)` sends `X` to `C c + X` inside the weighted support space. -/
example (c r : ℚ) :
    (weightedSupportPointTranslation (W := 0) (L := 2) Nat.one_pos c r
        ⟨X none, X_mem_weightedSupportSpace_test⟩ : DifferentialPolynomial ℚ 1) =
      C c + X none := by
  simp

/-- The constant exponent `0` is eligible for every positive cutoff. -/
theorem zero_mem_weightedSupportExponents_test :
    (0 : JetVariable 1 →₀ ℕ) ∈ weightedSupportExponents 1 1 0 1 Nat.one_pos := by
  simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree]

/-- The entry at the constant column and the row `0` is `1` at every point: the local
substitution fixes the constant `1`. -/
example (c r : ℚ) :
    weightedSupportLocalCoordinateMatrix (d := 1) (W := 0) (L := 1) 1 Nat.one_pos c r
      ⟨0, by simp [localContactOrder]⟩ ⟨0, zero_mem_weightedSupportExponents_test⟩ = 1 := by
  rw [weightedSupportLocalCoordinateMatrix_apply]
  simp [localConstraintCoordinatesAt, lowContactCoefficients]

/-- For `m = 0` there are no low-contact rows, so the rank is `0` at every point. -/
example (c r : ℚ) :
    (weightedSupportLocalCoordinateMatrix (d := 1) (W := 0) (L := 5) 0 Nat.one_pos c r).rank =
      0 := by
  have : IsEmpty (LowContactIndex 1 0) := ⟨fun e => Nat.not_lt_zero _ e.2⟩
  let := Fintype.ofIsEmpty (α := LowContactIndex 1 0)
  exact Nat.le_zero.mp ((Matrix.rank_le_card_height _).trans (by simp))

/-- Source shape `weightedSupportLocalCoordinateMatrix_zero_baseChange`, derived from the
coefficient-map theorem at the point `(0, 0)`. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E] (d m W D : ℕ) (L : ℝ) (hD : 0 < D) :
    weightedSupportLocalCoordinateMatrix (R := E) (d := d) (W := W) (L := L) m hD 0 0 =
      (weightedSupportLocalCoordinateMatrix (R := F) m hD 0 0).map (algebraMap F E) := by
  rw [weightedSupportLocalCoordinateMatrix_map, map_zero]

/-- Source shape `rank_weightedSupportLocalCoordinateMatrix_le_base_actual`: over an extension
field, the rank at any point is at most the base-field rank of the polynomial-valued constraint
map at `(0, 0)`, which in turn equals its rank at any base-field point. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E] (d m W D : ℕ) (L : ℝ) (hD : 0 < D)
    (center received : E) (center₀ received₀ : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (d := d) (W := W) (L := L) m hD center₀ received₀)) := by
  rw [finrank_range_weightedSupportLocalConstraint_eq_zero]
  exact rank_weightedSupportLocalCoordinateMatrix_le_base_actual m hD center received
