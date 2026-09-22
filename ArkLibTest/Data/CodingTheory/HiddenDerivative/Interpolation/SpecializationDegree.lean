/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SpecializationDegree

/-!
# Acceptance tests for the specialization degree of exact interpolation polynomials

With `D = 2`, `d = 1`, `A = 2`, `m = 1` and `M = W = 0`, the monomial `X` lies in the exact space.
Its specialization at any `P` of degree at most `2` is `X`, of degree `1 < 2`, as the theorem
predicts. When `m * A = 0` the space is `{0}`, and the positivity hypothesis of the degree bound is
needed because `0` has natural degree `0`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem hdD₁₂ : (1 : ℕ) < 2 := by decide

private theorem X_mem : (X none : DifferentialPolynomial ℚ 1) ∈
    exactInterpolationSpace ℚ 2 2 1 1 0 0 hdD₁₂ := by
  rw [X, monomial_mem_exactInterpolationSpace]
  left
  simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    Finsupp.weight_single, jetFirstWeight, jetHigherWeight]

/-- The monomial `X` specializes to `X`, whose degree `1` is below `m * A = 2`. -/
example (P : Polynomial ℚ) (hP : P.natDegree ≤ 2) :
    (differentialSpecialization (X none : DifferentialPolynomial ℚ 1) P).natDegree < 2 ∧
      differentialSpecialization (X none : DifferentialPolynomial ℚ 1) P = Polynomial.X :=
  ⟨natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace (by decide) hdD₁₂
    X_mem P hP, by simp [differentialSpecialization, differentialSpecializationHom]⟩

/-- The coefficient form at the coordinates of `X`. -/
example (P : Polynomial ℚ) (hP : P.natDegree ≤ 2) :
    (differentialSpecialization ((exactInterpolationPolynomial hdD₁₂
      ((exactInterpolationPolynomial hdD₁₂).symm ⟨X none, X_mem⟩)) :
        DifferentialPolynomial ℚ 1) P).natDegree < 1 * 2 :=
  natDegree_differentialSpecialization_exactInterpolationPolynomial_lt (by decide) hdD₁₂ _ P hP

/-- With `A = 0` the exact space is `{0}`. -/
example (Q : DifferentialPolynomial ℚ 1) (hQ : Q ∈ exactInterpolationSpace ℚ 2 0 1 3 0 0 hdD₁₂) :
    Q = 0 :=
  eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero (by decide) hdD₁₂ hQ

/-- The hypothesis `0 < m * A` is needed: at `A = 0` the zero polynomial is in the space and its
specialization has natural degree `0`, which is not below `m * A = 0`. -/
example (P : Polynomial ℚ) :
    (0 : DifferentialPolynomial ℚ 1) ∈ exactInterpolationSpace ℚ 2 0 1 3 0 0 hdD₁₂ ∧
      ¬ (differentialSpecialization (0 : DifferentialPolynomial ℚ 1) P).natDegree < 3 * 0 :=
  ⟨Submodule.zero_mem _, by simp⟩
