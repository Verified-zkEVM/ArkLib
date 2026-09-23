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

example : (taylor (1 : ZMod 2) (expand (ZMod 2) 2 X)).coeff 2 = 1 := by
  simpa [hasseDeriv_X] using
    coeff_taylor_expand_expChar_pow_mul (R := ZMod 2) 2 1 X 1 1

example : (taylor (1 : ZMod 2) (expand (ZMod 2) 2 X)).coeff 1 = 0 :=
  coeff_taylor_expand_expChar_pow_eq_zero (R := ZMod 2) 2 1 X 1 (by norm_num)

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

example : (0 : ℚ[X]) = 0 :=
  eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    (fun _ : Fin 1 => (0 : ℚ)) {0} 1 1
    (by
      intro i hi j hj hij
      exact Subsingleton.elim i j)
    (by norm_num) (by intro i hi; simp) (by simp)

example : (0 : ℚ[X]) = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    (fun _ : Fin 1 => (0 : ℚ)) {0} 1 1
    (by
      intro i hi j hj hij
      exact Subsingleton.elim i j)
    (by norm_num) (by intro i hi; simp) (by norm_num)

/-! ## Sparse contraction -/

example :
    expand ℚ 2 (contract 2 (X ^ 4 + 1 : ℚ[X])) = X ^ 4 + 1 := by
  apply (expand_contract_eq_self_iff 2 (X ^ 4 + 1 : ℚ[X])).2
  intro i hi
  rw [coeff_add, coeff_X_pow, coeff_one]
  have h4 : i ≠ 4 := by rintro rfl; exact hi ⟨2, rfl⟩
  have h0 : i ≠ 0 := by rintro rfl; exact hi ⟨0, rfl⟩
  simp [h4, h0]

example : (contract 2 (X ^ 2 + 1 : ℚ[X])).degree < 2 :=
  degree_contract_lt_of_degree_lt (X ^ 2 + 1) (by compute_degree!)

example : ∃! Q : ℚ[X], Q.degree < ↑(3 : ℕ) ∧ expand ℚ 2 Q = X ^ 4 + 1 := by
  apply existsUnique_expand_of_sparse (by norm_num) (X ^ 4 + 1)
  · intro i hi
    rw [coeff_add, coeff_X_pow, coeff_one]
    have h4 : i ≠ 4 := by rintro rfl; exact hi ⟨2, rfl⟩
    have h0 : i ≠ 0 := by rintro rfl; exact hi ⟨0, rfl⟩
    simp [h4, h0]
  · compute_degree!

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
