/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.RingTheory.Polynomial.GenericZeroPattern

/-!
# Acceptance tests for generic zero patterns and generic multiplicity patterns
-/

open Polynomial

/-- Three overlapping sets in `Fin 4`. -/
def testZeroPattern : Fin 3 → Finset (Fin 4) := ![{0, 1}, {1, 2}, {2, 3}]

/-- The three sets form a generic zero pattern. -/
theorem testZeroPattern_isGenericZeroPattern : Finset.IsGenericZeroPattern 3 testZeroPattern := by
  decide

/-- Over `ℚ`, the pattern is realised at distinct points. -/
example : ∃ α : Fin 4 ↪ ℚ, ∃ g : Fin 3 → ℚ[X], (∀ ℓ, g ℓ ∈ degreeLT ℚ 3) ∧
    (∀ ℓ, ∀ i ∈ testZeroPattern ℓ, (g ℓ).eval (α i) = 0) ∧ LinearIndependent ℚ g :=
  exists_embedding_linearIndependent_of_isGenericZeroPattern
    testZeroPattern_isGenericZeroPattern

/-- A generic zero pattern with a set of size `1 < 3 - 1`, so the realisation pads it first. -/
example : ∃ α : Fin 4 ↪ ℚ, ∃ g : Fin 3 → ℚ[X], (∀ ℓ, g ℓ ∈ degreeLT ℚ 3) ∧
    (∀ ℓ, ∀ i ∈ (![{0}, {1, 2}, {2, 3}] : Fin 3 → Finset (Fin 4)) ℓ, (g ℓ).eval (α i) = 0) ∧
    LinearIndependent ℚ g :=
  exists_embedding_linearIndependent_of_isGenericZeroPattern (by decide)

/-- A multiplicity pattern with multiplicity `2` at the point `1`. -/
def testMultiplicityPattern : Fin 2 → Multiset (Fin 2) := ![{1, 1}, {0}]

/-- It is a generic multiplicity pattern of dimension `3`. -/
theorem testMultiplicityPattern_isGenericMultiplicityPattern :
    Multiset.IsGenericMultiplicityPattern 3 testMultiplicityPattern :=
  ⟨by decide, by unfold testMultiplicityPattern; decide⟩

/-- All its multiplicities are at most one except at `1`. -/
theorem testMultiplicityPattern_countLeOneExcept :
    Multiset.CountLeOneExcept 1 testMultiplicityPattern := by
  unfold Multiset.CountLeOneExcept testMultiplicityPattern
  decide

/-- The three polynomials `(X - a₁)²`, `X - a₀` and `X (X - a₀)` are linearly independent. -/
example : LinearIndependent (MvPolynomial (Fin 2) ℚ)
    (vanishingFamily (MvPolynomial.X (R := ℚ)) 3 testMultiplicityPattern) :=
  linearIndependent_vanishingFamily testMultiplicityPattern_isGenericMultiplicityPattern
    testMultiplicityPattern_countLeOneExcept
