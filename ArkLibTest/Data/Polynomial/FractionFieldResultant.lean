/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldResultant
import Mathlib.Algebra.Field.ZMod

/-! The padded resultant includes the derivative-degree drop in small characteristic,
the degree-one boundary, and fraction-field separability without ring separability. -/

open Polynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def artinSchreier : (ZMod 3)[X] := X ^ 3 - X

private theorem artinSchreier_derivative : artinSchreier.derivative = -1 := by
  have hthree : ((3 : ℕ) : ZMod 3) = 0 := CharP.cast_eq_zero _ 3
  simp only [artinSchreier, derivative_sub, derivative_pow, derivative_X]
  rw [hthree]
  simp

private theorem artinSchreier_separable : artinSchreier.Separable := by
  rw [separable_def, artinSchreier_derivative]
  exact ⟨0, -1, by simp⟩

example : artinSchreier.derivative.natDegree < artinSchreier.natDegree - 1 := by
  rw [artinSchreier_derivative]
  norm_num [artinSchreier, natDegree_sub_eq_left_of_natDegree_lt]

example : resultant artinSchreier artinSchreier.derivative 3 2 ≠ 0 := by
  have h := resultant_derivative_ne_zero_of_separable_map_fractionField
    (K := ZMod 3) artinSchreier (by simpa using artinSchreier_separable)
  simpa [artinSchreier, natDegree_sub_eq_left_of_natDegree_lt] using h

example : resultant (X : ℚ[X]) (X : ℚ[X]).derivative 1 0 ≠ 0 := by
  have hsep : ((X : ℚ[X]).map (algebraMap ℚ ℚ)).Separable := by
    simpa using (separable_X : (X : ℚ[X]).Separable)
  convert resultant_derivative_ne_zero_of_separable_map_fractionField (X : ℚ[X]) hsep
    using 1
  simp

example : resultant (C 2 : ℚ[X]) (C 2 : ℚ[X]).derivative 0 0 ≠ 0 := by
  have hsep : ((C 2 : ℚ[X]).map (algebraMap ℚ ℚ)).Separable := by
    simp [separable_C]
  convert resultant_derivative_ne_zero_of_separable_map_fractionField (C 2 : ℚ[X]) hsep
    using 1
  simp

-- 2Y has no Bezout identity with its derivative over Z, but is separable over Q.
example : resultant (C 2 * X : ℤ[X]) (C 2 * X : ℤ[X]).derivative 1 0 ≠ 0 := by
  have hsep : ((C 2 * X : ℤ[X]).map (algebraMap ℤ ℚ)).Separable := by
    rw [separable_def]
    refine ⟨0, C (1 / 2), ?_⟩
    norm_num
    rw [← C_ofNat, ← C_mul]
    norm_num
  have h := resultant_derivative_ne_zero_of_separable_map_fractionField (K := ℚ)
    (C 2 * X : ℤ[X]) hsep
  convert h using 1
  simp

-- The actual-degree certificate also covers derivative degree drop in characteristic two.
example : resultant (X ^ 2 + X : Polynomial (ZMod 2))
    (X ^ 2 + X : Polynomial (ZMod 2)).derivative ≠ 0 := by
  apply resultant_derivative_ne_zero_of_fractionField_separable (K := ZMod 2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  simpa [separable_def, one_add_one_eq_two, htwo] using
    (isCoprime_one_right : IsCoprime (X ^ 2 + X : Polynomial (ZMod 2)) 1)

-- The specialization criterion needs positive combined degree: two zero constants fail it.
example : resultant (0 : Polynomial (ZMod 2)) 0 = 1 ∧
    ¬ IsCoprime (0 : Polynomial (ZMod 2)) 0 := by
  exact ⟨by simp, not_isCoprime_zero_zero⟩
