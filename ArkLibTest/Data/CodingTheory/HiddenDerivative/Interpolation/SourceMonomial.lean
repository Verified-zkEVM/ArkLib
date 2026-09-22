/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SourceMonomial

/-!
# Source monomial acceptance tests

At `d = 1` the source monomial `X² Y₀ Y₁³` has jet degree `1 + 3 = 4`, independent of the power
of `X`. For the weight that also counts `X` it has degree `2 + 1 + 3 = 6`, and it is not
homogeneous of degree four for that weight.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- `X² Y₀ Y₁³` has jet degree four. -/
example : (sourceMonomial (R := ℚ) (d := 1) 2 1 ![3]).IsWeightedHomogeneous jetDegreeWeight 4 := by
  simpa using sourceMonomial_isWeightedHomogeneous_jetDegreeWeight (R := ℚ) (d := 1) 2 1 ![3]

/-- For the weight that gives every variable weight one, `X² Y₀ Y₁³` has degree six. -/
example : (sourceMonomial (R := ℚ) (d := 1) 2 1 ![3]).IsWeightedHomogeneous
    (fun _ : JetVariable 1 => (1 : ℕ)) 6 := by
  simpa using sourceMonomial_isWeightedHomogeneous (R := ℚ) (fun _ : JetVariable 1 => (1 : ℕ))
    2 1 ![3]

/-- The degree depends on the weight: `X² Y₀ Y₁³` is not homogeneous of degree four when `X`
has weight one. -/
example : ¬ (sourceMonomial (R := ℚ) (d := 1) 2 1 ![3]).IsWeightedHomogeneous
    (fun _ : JetVariable 1 => (1 : ℕ)) 4 := by
  intro h4
  have h6 := sourceMonomial_isWeightedHomogeneous (R := ℚ) (fun _ : JetVariable 1 => (1 : ℕ))
    2 1 ![3]
  have hne : sourceMonomial (R := ℚ) (d := 1) 2 1 ![3] ≠ 0 := by
    simp [sourceMonomial, X_ne_zero]
  have := h4.inj_right hne h6
  simp at this
