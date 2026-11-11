/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.EventualGrowth
import ArkLib.ToMathlib.Polynomial.FrobeniusTaylor
import ArkLib.ToMathlib.Polynomial.RectangleDifference
import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import ArkLib.ToMathlib.Polynomial.SparseContraction
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! # Polynomial acceptance tests -/

open Polynomial Filter

namespace PolynomialTest

example : (backwardDifference (3 : ℚ) (X ^ 2)).eval 5 = 21 := by
  norm_num [eval_backwardDifference]

example :
    (backwardDifference (3 : ℚ) (X ^ 2 : ℚ[X])).natDegree = (X ^ 2 : ℚ[X]).natDegree - 1 ∧
      (backwardDifference (3 : ℚ) (X ^ 2 : ℚ[X])).leadingCoeff =
        (3 : ℚ) * (X ^ 2 : ℚ[X]).natDegree * (X ^ 2 : ℚ[X]).leadingCoeff :=
  natDegree_backwardDifference_eq_and_leadingCoeff (b := (3 : ℚ)) (P := X ^ 2) (by norm_num)

example :
    ((X ^ 2 : ℚ[X]).comp (C 2 * X + C 1)).natDegree = (X ^ 2 : ℚ[X]).natDegree :=
  natDegree_comp_C_mul_X_add_C (X ^ 2) (by norm_num) 1

private theorem eventually_eval_X_nonneg :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (X : ℚ[X]).eval (n : ℚ) :=
  Filter.Eventually.of_forall fun n => by
    simpa only [eval_X] using (show 0 ≤ (n : ℚ) by exact_mod_cast Nat.zero_le n)

private theorem eventually_eval_X_le_twoX :
    ∀ᶠ n : ℕ in atTop,
      (X : ℚ[X]).eval (n : ℚ) ≤ ((C (2 : ℚ) * X : ℚ[X])).eval (n : ℚ) :=
  Filter.Eventually.of_forall fun n => by
    simp only [eval_mul, eval_C, eval_X]
    have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    nlinarith [hn]

private theorem eventually_eval_X_le_Xsq :
    ∀ᶠ n : ℕ in atTop, (X : ℚ[X]).eval (n : ℚ) ≤ (X ^ 2 : ℚ[X]).eval (n : ℚ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [eval_X, eval_pow]
  have hn' : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

private theorem eventually_eval_X_le_shifted_Xsq :
    ∀ᶠ n : ℕ in atTop,
      (X : ℚ[X]).eval (n : ℚ) ≤
        (X ^ 2 : ℚ[X]).eval ((1 : ℚ) * (n : ℚ) + 1) :=
  Filter.Eventually.of_forall fun n => by
    simp only [eval_X, eval_pow]
    have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    nlinarith [hn]

private theorem eventually_eval_twoX_le_threeX :
    ∀ᶠ n : ℕ in atTop,
      ((C (2 : ℚ) * X : ℚ[X])).eval (n : ℚ) ≤
        (3 : ℚ) * (X : ℚ[X]).eval ((1 : ℚ) * (n : ℚ) + 0) :=
  Filter.Eventually.of_forall fun n => by
    simp only [eval_mul, eval_C, eval_X]
    have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    nlinarith [hn]

private theorem eventually_eval_X_le_backwardDifference_Xsq :
    ∀ᶠ n : ℕ in atTop,
      (X : ℚ[X]).eval (n : ℚ) ≤ (backwardDifference 1 (X ^ 2 : ℚ[X])).eval (n : ℚ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [eval_backwardDifference]
  simp only [eval_pow, eval_X]
  have hn' : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

example : 0 ≤ (X : ℚ[X]).leadingCoeff :=
  leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg eventually_eval_X_nonneg

example :
    (X : ℚ[X]).natDegree ≤ (C (2 : ℚ) * X : ℚ[X]).natDegree ∧
      ((X : ℚ[X]).natDegree = (C (2 : ℚ) * X : ℚ[X]).natDegree →
        (X : ℚ[X]).leadingCoeff ≤ (C (2 : ℚ) * X : ℚ[X]).leadingCoeff) :=
  natDegree_le_of_eventually_eval_natCast_le eventually_eval_X_nonneg
    eventually_eval_X_le_twoX

example :
    (X : ℚ[X]).natDegree ≤ (X ^ 2 : ℚ[X]).natDegree - 1 ∧
      (X : ℚ[X]).coeff ((X ^ 2 : ℚ[X]).natDegree - 1) ≤
        (1 : ℚ) * (X ^ 2 : ℚ[X]).natDegree * (X ^ 2 : ℚ[X]).leadingCoeff :=
  natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference
    eventually_eval_X_nonneg eventually_eval_X_le_backwardDifference_Xsq

example : (X : ℚ[X]).natDegree ≤ (X ^ 2 : ℚ[X]).natDegree * (X : ℚ[X]).natDegree :=
  natDegree_le_of_eventually_eval_natCast_le_mul_eval_comp (P := X ^ 2) (S := X) (m := 1)
    eventually_eval_X_nonneg (eventually_eval_X_le_Xsq.mono fun n h => by
      simpa only [eval_X, one_mul] using h)

example : (X : ℚ[X]).natDegree ≤ (X ^ 2 : ℚ[X]).natDegree :=
  natDegree_le_of_eventually_eval_natCast_le_mul_eval_affine (P := X ^ 2) (m := 1) (c := 1) (d := 1)
    eventually_eval_X_nonneg (eventually_eval_X_le_shifted_Xsq.mono fun n h => by
      simpa only [one_mul] using h)

example : (C (2 : ℚ) * X : ℚ[X]).natDegree = (X : ℚ[X]).natDegree :=
  natDegree_eq_of_eventually_eval_natCast_le_of_le_mul_eval_affine
    (P := X) (Q := (C (2 : ℚ) * X : ℚ[X])) (m := 3) (c := 1) (d := 0) eventually_eval_X_nonneg
    eventually_eval_X_le_twoX eventually_eval_twoX_le_threeX

example : (X : ℚ[X]).coeff 1 ≤ (C (2 : ℚ) * X : ℚ[X]).coeff 1 :=
  coeff_le_of_natDegree_le_of_eventually_eval_natCast_le (d := 1)
    (by simp [natDegree_X])
    (by rw [natDegree_C_mul_X (2 : ℚ) (by norm_num)])
    eventually_eval_X_le_twoX

example : (0 : ℚ) ≤ (X - 1 : ℚ[X]).coeff 1 :=
  coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
    (by compute_degree!) ((eventually_ge_atTop 1).mono fun N hN ↦ by
      have : (1 : ℚ) ≤ N := by exact_mod_cast hN
      simp only [eval_sub, eval_X, eval_one]
      linarith)

example : (taylor (3 : ℚ) (X ^ 2)).coeff 2 = 1 ∧
    (taylor (3 : ℚ) (X ^ 2)).coeff 5 = 0 := by
  constructor
  · rw [coeff_taylor_of_natDegree_le _ (natDegree_X_pow_le 2), coeff_X_pow_self]
  · rw [coeff_taylor_of_natDegree_le _ ((natDegree_X_pow_le 2).trans (by norm_num)), coeff_X_pow]
    norm_num

example : taylor (1 : ZMod 2) (expand (ZMod 2) 2 X) = X ^ 2 + 1 := by
  have h := taylor_expand_expChar_pow (R := ZMod 2) 2 1 X 1
  simp only [pow_one, one_pow] at h
  rw [h, taylor_X, map_add, expand_X, expand_C, C_1]

/-! ## Rectangle differences -/

example : (rectangleDifference 1 (1 : ℚ) 1 1 1).natDegree ≤ 1 :=
  natDegree_rectangleDifference_le 1 1 1 1 1

example : (rectangleDifference 1 (1 : ℚ) 1 1 1).coeff 1 = 2 := by
  norm_num [coeff_rectangleDifference_self]

example :
    (rectangleDifference 1 ((1 : ℕ) : ℚ) (1 : ℕ) (1 : ℕ) (1 : ℕ)).eval ((3 : ℕ) : ℚ) = 7 := by
  rw [eval_rectangleDifference_natCast 1 1 1 1 1 3 (by norm_num) (by norm_num)]
  norm_num [Nat.choose_one_right]

/-! ## Root multiplicities -/

example :
    (∑ a ∈ ({0} : Finset ℤ), (X : ℤ[X]).rootMultiplicity a) ≤ (X : ℤ[X]).natDegree :=
  sum_rootMultiplicity_le_natDegree ({0} : Finset ℤ)

/-! ## Sparse contraction -/

private theorem quartic_sparse_for_two :
    ∀ i : ℕ, ¬2 ∣ i → (X ^ 4 + 1 : ℚ[X]).coeff i = 0 := by
  intro i hi
  rw [coeff_add, coeff_X_pow, coeff_one]
  have h4 : i ≠ 4 := by rintro rfl; exact hi ⟨2, rfl⟩
  have h0 : i ≠ 0 := by rintro rfl; exact hi ⟨0, rfl⟩
  simp [h4, h0]

example :
    expand ℚ 2 (contract 2 (X ^ 4 + 1 : ℚ[X])) = X ^ 4 + 1 := by
  exact (expand_contract_eq_self_iff 2 (X ^ 4 + 1 : ℚ[X])).2 quartic_sparse_for_two

example : (contract 2 (X ^ 2 + 1 : ℚ[X])).degree < 2 :=
  degree_contract_lt_of_degree_lt (X ^ 2 + 1) (by compute_degree!)

example : ∃! Q : ℚ[X], Q.degree < ↑(3 : ℕ) ∧ expand ℚ 2 Q = X ^ 4 + 1 := by
  apply existsUnique_expand_of_sparse (by norm_num) (X ^ 4 + 1) quartic_sparse_for_two
  compute_degree!

example :
    ∃! Q : (ZMod 2)[X], Q.degree < ↑(2 : ℕ) ∧
      expand (ZMod 2) (2 ^ 1) Q = X ^ 2 + 1 := by
  apply existsUnique_expand_of_sparse_taylor 2 1 2 (X ^ 2 + 1) 1
  · intro i hi
    have hT : taylor (1 : ZMod 2) (X ^ 2 + 1) = X ^ 2 := by
      rw [taylor_apply, add_comp, pow_comp, X_comp, one_comp, C_1, add_pow_char, one_pow,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hT, coeff_X_pow]
    have : i ≠ 2 := by rintro rfl; exact hi ⟨1, rfl⟩
    simp [this]
  · compute_degree!

end PolynomialTest
