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

The canonical basis vector of `restrictSupport` at `X 0` is the monomial `X 0`. With weight `3` on
`X 0`, the bound `7` gives degree at most `7 / 3 = 2` in `X 0`, attained by `X 0 ^ 2`; the
positivity hypothesis on the weight is needed, since with weight `0` on `X 0` the polynomial
`X 0 ^ 5` has weight `0` but degree `5` in `X 0`.
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

/-- The basis vector at the exponent `X 0` is the monomial `X 0`. -/
example : (basisRestrictSupport ℚ ({Finsupp.single 0 1} : Set (Fin 1 →₀ ℕ))
    ⟨Finsupp.single 0 1, rfl⟩ : MvPolynomial (Fin 1) ℚ) = X 0 := by
  rw [coe_basisRestrictSupport_apply]
  rfl

/-- With weight `3` on `X 0` and bound `7`, the degree in `X 0` is at most `2`, as for `X 0 ^ 2`. -/
example : degreeOf 0 (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ≤ 2 ∧
    (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![3, 1] 7 := by
  have hmem : (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![3, 1] 7 :=
    restrictWeightAtMost_mono _ (by norm_num : (6 : ℕ) ≤ 7)
      (pow_mem_restrictWeightAtMost (X_mem_restrictWeightAtMost (R := ℚ) ![3, 1] 0 le_rfl) 2)
  exact ⟨degreeOf_le_div_of_mem_restrictWeightAtMost hmem (by norm_num), hmem⟩

/-- The weight of `X 0` must be positive: with weight `0`, `X 0 ^ 5` has weight at most `0` but
degree `5` in `X 0`, which exceeds `0 / 0 = 0`. -/
example : (X 0 ^ 5 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![0, 1] 0 ∧
    ¬ degreeOf 0 (X 0 ^ 5 : MvPolynomial (Fin 2) ℚ) ≤ 0 / 0 := by
  refine ⟨restrictWeightAtMost_mono _ (by norm_num : 5 • (0 : ℕ) ≤ 0)
    (pow_mem_restrictWeightAtMost (X_mem_restrictWeightAtMost (R := ℚ) ![0, 1] 0 le_rfl) 5), ?_⟩
  rw [degreeOf_X_self_pow]
  decide
