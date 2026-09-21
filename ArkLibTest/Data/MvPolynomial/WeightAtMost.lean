/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightAtMost

/-!
# Signed weight bound acceptance tests

With the weight `X 0 ↦ -1, X 1 ↦ 1`, the product `X 0 * X 1` has weight `0`; the constant `1`
violates a negative bound, which is why `C_mem_restrictWeightAtMost` requires `0 ≤ a`; and the
coefficient space of a two-element exponent set has dimension `2`.
-/

open MvPolynomial

/-- A negative weight cancels a positive one under multiplication. -/
example : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![(-1 : ℤ), 1] 0 := by
  simpa using mul_mem_restrictWeightAtMost
    (X_mem_restrictWeightAtMost (R := ℚ) ![(-1 : ℤ), 1] (a := -1) 0 le_rfl)
    (X_mem_restrictWeightAtMost (R := ℚ) ![(-1 : ℤ), 1] (a := 1) 1 le_rfl)

/-- A constant has weight `0`, so it fails the bound `-1`. -/
example : (C 1 : MvPolynomial (Fin 2) ℚ) ∉ restrictWeightAtMost ![(-1 : ℤ), 1] (-1) := by
  rw [← monomial_zero', monomial_mem_restrictWeightAtMost]
  simp

/-- The exponents `0` and `X 0` span a two-dimensional space. -/
example : Module.finrank ℚ (restrictSupport ℚ
    (↑({0, Finsupp.single 0 1} : Finset (Fin 1 →₀ ℕ)) : Set (Fin 1 →₀ ℕ))) = 2 := by
  rw [finrank_restrictSupport_finset, Finset.card_pair]
  exact (Finsupp.single_ne_zero.mpr one_ne_zero).symm
