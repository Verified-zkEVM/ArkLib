/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Space

/-!
# First-order interpolation space acceptance tests

Membership of concrete exponents, including the case `D = 1` where `Y₁` has specialization
weight zero and only the total jet cap `μ` bounds its powers; the embedding into the exact
interpolation space; and a case showing that the embedding with a larger degree bound needs the
agreement threshold to grow.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- `X Y₀` has specialization weight `1 + 2 = 3 < 4` at `D = 2`, `m A = 4`, and jet degree
`1 ≤ μ`. -/
example : Finsupp.single none 1 + Finsupp.single (some 0) 1 ∈ firstOrderExponents 2 2 2 0 1 := by
  rw [mem_firstOrderExponents_iff_coordinates]
  simp

/-- At `D = 1`, `Y₁` has specialization weight `0`, so `Y₁⁵` is eligible once `μ ≥ 5`. -/
example : Finsupp.single (some 1) 5 ∈ firstOrderExponents 1 1 1 10 5 := by
  rw [mem_firstOrderExponents_iff_coordinates]
  simp

/-- At `D = 1`, `Y₁⁵` is not eligible when `μ = 4`: the total jet cap is what keeps the support
finite for `D ≤ 1`. -/
example : Finsupp.single (some 1) 5 ∉ firstOrderExponents 1 1 1 10 4 := by
  rw [mem_firstOrderExponents_iff_coordinates]
  simp

/-- The first-order support is finite at `D = 0` as well. -/
example : (firstOrderExponentSet 0 3 2 1 4).Finite := firstOrderExponentSet_finite 0 3 2 1 4

/-- The monomial `Y₁` lies in the first-order space at `D = 2`, `A = 2`, `m = 1`, `M = 1`,
`μ = 1`, since its specialization weight is `1 < 2`. -/
example : monomial (Finsupp.single (some 1) 1) (1 : ℚ) ∈ firstOrderSpace ℚ 2 2 1 1 1 := by
  rw [monomial_mem_firstOrderSpace, ← mem_firstOrderExponents,
    mem_firstOrderExponents_iff_coordinates]
  simp

/-- For `1 < D` the first-order space lies in the exact interpolation space with `d = 1`. -/
example {F : Type*} [CommSemiring F] {A m M μ W : ℕ} :
    firstOrderSpace F 3 A m M μ ≤ exactInterpolationSpace F 3 A 1 m M W (by norm_num) :=
  firstOrderSpace_le_exactInterpolationSpace (by norm_num)

/-- `Y₀` lies in the first-order space at `D = 1`, `A = 2`, `m = 1`, `M = 0`, `μ = 1` (weight
`1 < 2`), but not in the exact space with degree bound `2` and the same `A = 2` (weight `2`).
So `firstOrderSpace_le_exactInterpolationSpace_of_le` needs `m A + (D' - D) μ ≤ m A'`, which
fails here as `2 + 1 > 2`. -/
example : monomial (Finsupp.single (some 0) 1) (1 : ℚ) ∈ firstOrderSpace ℚ 1 2 1 0 1 ∧
    monomial (Finsupp.single (some 0) 1) (1 : ℚ) ∉
      exactInterpolationSpace ℚ 2 2 1 1 0 0 (by norm_num) := by
  refine ⟨?_, ?_⟩
  · rw [monomial_mem_firstOrderSpace, ← mem_firstOrderExponents,
      mem_firstOrderExponents_iff_coordinates]
    simp
  · rw [monomial_mem_exactInterpolationSpace]
    simp [ExactInterpolationEligibleExponent, weight_differentialWeight_eq]

/-- With the threshold raised to `A' = 3`, `m A + (D' - D) μ = 3 ≤ 3`, and the embedding holds. -/
example : firstOrderSpace ℚ 1 2 1 0 1 ≤ exactInterpolationSpace ℚ 2 3 1 1 0 0 (by norm_num) :=
  firstOrderSpace_le_exactInterpolationSpace_of_le (by norm_num) (by norm_num) (by norm_num)

/-- Members of the first-order space have specialization-weighted degree below `m A` and total jet
degree at most `μ`. -/
example {Q : DifferentialPolynomial ℚ 1} (hQ : Q ∈ firstOrderSpace ℚ 2 3 1 0 1) :
    differentialWeightedDegree 2 Q < 3 ∧ jetTotalDegree Q ≤ 1 :=
  ⟨differentialWeightedDegree_lt_of_mem_firstOrderSpace (by norm_num) hQ,
    jetTotalDegree_le_of_mem_firstOrderSpace hQ⟩
