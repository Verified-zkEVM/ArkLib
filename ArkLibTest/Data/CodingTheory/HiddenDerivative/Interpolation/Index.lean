/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index

/-!
# Exact interpolation space acceptance tests

For `D = 2`, `d = 1`, `A = 2`, `m = 1`, and `M = W = 0`, the eligible monomials are those of
specialization weight below `2` with no `Y₁`: `X` is eligible, while `X²`, `Y₀` (weight `2`), and
`Y₁` (weight `1` but excluded by `M = 0`) are not. At the boundary `D = d = 0` every power of
`Y₀` has weight zero, so the eligible set is infinite; this is why the space is indexed by a
proof of `d < D`. The coarse bound `weight_le_add_mul_totalJetDegree` is attained on `Y₀` and
strict on `Y₁`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem hdD₁₂ : (1 : ℕ) < 2 := by decide

/-- `X` is eligible, so its monomials lie in the space. -/
example (a : ℚ) :
    monomial (Finsupp.single none 1) a ∈ exactInterpolationSpace ℚ 2 2 1 1 0 0 hdD₁₂ := by
  rw [monomial_mem_exactInterpolationSpace]
  left
  simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    Finsupp.weight_single, jetFirstWeight, jetHigherWeight]

/-- `X²` has specialization weight `2`, which is not below `m * A = 2`. -/
example : ¬ExactInterpolationEligibleExponent 2 2 1 1 0 0 (Finsupp.single none 2) := by
  simp [ExactInterpolationEligibleExponent, Finsupp.weight_single]

/-- `Y₀` has weight `D = 2` and is not eligible. -/
example : ¬ExactInterpolationEligibleExponent 2 2 1 1 0 0 (Finsupp.single (some 0) 1) := by
  simp [ExactInterpolationEligibleExponent, Finsupp.weight_single]

/-- `Y₁` has weight `D - 1 = 1 < 2` but is excluded by the first-jet cap `M = 0`. -/
example : ¬ExactInterpolationEligibleExponent 2 2 1 1 0 0 (Finsupp.single (some 1) 1) := by
  simp [ExactInterpolationEligibleExponent, firstJetExponent, Finsupp.weight_single,
    jetFirstWeight]

/-- The jet-degree floor `⌊(mA - 1)/(D - d)⌋` at `D = 3`, `d = 1`, `m = 2`, `A = 3` is `2`. -/
example : exactInterpolationJetDegreeFloor 3 3 1 2 = 2 := by decide

/-- At `D = d = 0` the eligible set is infinite: every power of `Y₀` is eligible. -/
example : (exactInterpolationExponentSet 0 1 0 1 0 0).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => Finsupp.single (some 0 : JetVariable 0) n)
    (Finsupp.single_injective _) fun n => ?_
  simp [exactInterpolationExponentSet, ExactInterpolationEligibleExponent, firstJetExponent,
    fullHigherJetWeight, Finsupp.weight_single, jetFirstWeight, jetHigherWeight]

/-- Source shape: every individual jet degree of a member is bounded by the floor. -/
example {F : Type*} [Field F] {D A d m M W : ℕ} (hdD : d < D)
    {Q : DifferentialPolynomial F d} (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (j : Fin (d + 1)) :
    MvPolynomial.degreeOf (some j) Q ≤ (m * A - 1) / (D - d) :=
  jetDegree_le_floor_of_mem_exactInterpolationSpace hdD hQ j

/-- The specialization weight bound needs `0 < m * A`; with it, members have weighted degree
below `m * A`. -/
example {Q : DifferentialPolynomial ℚ 1}
    (hQ : Q ∈ exactInterpolationSpace ℚ 2 2 1 1 0 0 hdD₁₂) :
    differentialWeightedDegree 2 Q < 2 :=
  differentialWeightedDegree_lt_of_mem_exactInterpolationSpace (by decide) hdD₁₂ hQ

/-- A single coefficient column is evaluated on its monomial. -/
example (eval : DifferentialPolynomial ℚ 1 →ₗ[ℚ] ℚ)
    (u : ExactInterpolationIndex 2 2 1 1 0 0 hdD₁₂) (a : ℚ) :
    exactInterpolationCoefficientEvaluator hdD₁₂ eval (Finsupp.single u a) =
      eval (monomial u.1 a) :=
  exactInterpolationCoefficientEvaluator_single hdD₁₂ eval u a

/-- The exponent split: `X² Y₀ Y₁³` has degree `2 + 4`. -/
example :
    (Finsupp.single none 2 + Finsupp.single (some 0) 1 + Finsupp.single (some 1) 3 :
        JetVariable 1 →₀ ℕ).degree = 6 := by
  rw [degree_eq_add_totalJetDegree, totalJetDegree_eq_sum]
  simp [Fin.sum_univ_two]

/-- The coarse bound `weight_le_add_mul_totalJetDegree` is attained on `Y₀`: at `D = 3` both
sides equal `3`. -/
example : Finsupp.weight (differentialWeight 3) (Finsupp.single (some 0) 1 : JetVariable 1 →₀ ℕ) =
    (Finsupp.single (some 0) 1 : JetVariable 1 →₀ ℕ) none +
      3 * totalJetDegree (Finsupp.single (some 0) 1 : JetVariable 1 →₀ ℕ) := by
  rw [weight_differentialWeight_eq, totalJetDegree_eq_sum]
  simp [Fin.sum_univ_two]

/-- The coarse bound is strict on `Y₁`: at `D = 3` the specialization weight is `2`, below `3`. -/
example : Finsupp.weight (differentialWeight 3) (Finsupp.single (some 1) 1 : JetVariable 1 →₀ ℕ) <
    (Finsupp.single (some 1) 1 : JetVariable 1 →₀ ℕ) none +
      3 * totalJetDegree (Finsupp.single (some 1) 1 : JetVariable 1 →₀ ℕ) := by
  rw [weight_differentialWeight_eq, totalJetDegree_eq_sum]
  simp [Fin.sum_univ_two]
