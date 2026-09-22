/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneity under substitution and filters

Two variables of weight two are sent to the degree-two monomials `X₀ X₁` and `X₀²` for the
standard grading, so the degree-four monomial `X₀ X₁` goes to a polynomial of standard degree
four. Sending a variable of degree one to the constant `1` breaks homogeneity, so the generator
hypothesis of `IsWeightedHomogeneous.bind₁` cannot be dropped. A support filter keeps
homogeneity even when it keeps only part of a homogeneous polynomial.
-/

open MvPolynomial

/-- Generators of weight two go to monomials of standard degree two, so `X₀ X₁`, of weight four,
goes to a polynomial of standard degree four. -/
example : (bind₁ ![(X 0 * X 1 : MvPolynomial (Fin 2) ℚ), X 0 ^ 2] (X 0 * X 1)).IsWeightedHomogeneous
    (fun _ => (1 : ℕ)) 4 := by
  have hφ : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ).IsWeightedHomogeneous (fun _ => (2 : ℕ)) 4 :=
    (isWeightedHomogeneous_X ℚ _ 0).mul (isWeightedHomogeneous_X ℚ _ 1)
  refine hφ.bind₁ fun i => ?_
  fin_cases i
  · exact (isWeightedHomogeneous_X ℚ _ 0).mul (isWeightedHomogeneous_X ℚ _ 1)
  · exact (isWeightedHomogeneous_X ℚ _ 0).pow 2

/-- The generator hypothesis is needed: sending `X₀`, of degree one, to the constant `1` gives a
polynomial that is not homogeneous of degree one. -/
example : ¬ (bind₁ (fun _ => (1 : MvPolynomial (Fin 1) ℚ)) (X 0)).IsWeightedHomogeneous
    (fun _ => (1 : ℕ)) 1 := by
  intro h
  have h0 := @h 0 (by simp)
  simp at h0

/-- Keeping only the monomials divisible by `X₀` keeps homogeneity of degree two. -/
example : (filterSupport (fun e : Fin 2 →₀ ℕ => 0 < e 0)
    (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)).IsWeightedHomogeneous
      (fun _ => (1 : ℕ)) 2 := by
  have hX := isWeightedHomogeneous_X ℚ (fun _ : Fin 2 => (1 : ℕ))
  exact ((((hX 0).pow 2).add ((hX 0).mul (hX 1))).add ((hX 1).pow 2)).filterSupport _

/-- A weighted truncation is a support filter, so it preserves homogeneity for a different
weight: truncating by `X₀`-degree below one keeps standard degree two. -/
example : (weightedTruncation (fun i : Fin 2 => if i = 0 then 1 else 0) 1
    (X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)).IsWeightedHomogeneous
      (fun _ => (1 : ℕ)) 2 := by
  have hX := isWeightedHomogeneous_X ℚ (fun _ : Fin 2 => (1 : ℕ))
  exact (((hX 0).mul (hX 1)).add ((hX 1).pow 2)).weightedTruncation _ 1
