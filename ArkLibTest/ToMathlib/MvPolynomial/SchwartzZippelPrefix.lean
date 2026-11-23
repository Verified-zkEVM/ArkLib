/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.MvPolynomial.SchwartzZippelPrefix
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation

/-!
# Sequential Schwartz–Zippel acceptance tests

On `(ZMod 3)²`:

* for `X 1 - X 0 - 1` and `I = {1}`, substituting `x 0` leaves `X 1 - C (x 0) - 1 ≠ 0`, and
  substituting `x 1` as well gives `0` exactly when `x 1 = x 0 + 1`. Three of the six pairs with
  distinct coordinates do so, which attains `card_filter_injective_sequential_le`:
  `3 * (3 - 1) = 1 * 6`;
* for `X 0 * X 1` and `I = {1}`, substituting `x 0` leaves `C (x 0) * X 1`, which is nonzero exactly
  when `x 0 ≠ 0`. So of the four zeros with distinct coordinates, the two with `x 0 = 0` are not
  counted. Counting them would give `4 * (3 - 1) = 8 > 6 = 1 * 6`, so the bound needs the
  condition that `P i` is nonzero after substituting the coordinates before `i`;
* for `P 0 = X 0`, `P 1 = X 1 - X 0 - 1` and `I = {0, 1}`, only `(0, 1)` is counted, which attains
  the bound: `1 * (3 * 2) = (1 * 1) * 6`.
-/

open Finset MvPolynomial

/-- `X 1 - C a - 1` is nonzero. -/
private theorem X_one_sub_C_sub_one_ne_zero (a : ZMod 3) :
    (X 1 - C a - 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 := fun h ↦ by
  have h1 := congrArg (fun q ↦ q.coeff (Finsupp.single 1 1)) h
  simp [coeff_X, coeff_C, coeff_one, (Finsupp.single_ne_zero.mpr one_ne_zero).symm] at h1

/-- The degree of `X 1 - X 0 - 1` in `X 1` is `1`. -/
private theorem degreeOf_X_one_sub_X_zero_sub_one :
    (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)).degreeOf 1 = 1 := by
  refine le_antisymm ((degreeOf_sub_le _ _ _).trans <| max_le ((degreeOf_sub_le _ _ _).trans
    (max_le (by simp) (by simp [degreeOf_X]))) (by simp)) ?_
  refine le_of_eq_of_le ?_ (monomial_le_degreeOf 1 (m := Finsupp.single 1 1) ?_)
  · simp
  · rw [mem_support_iff]
    simp [coeff_X, coeff_one, Finsupp.single_eq_single_iff,
      (Finsupp.single_ne_zero.mpr one_ne_zero).symm]

/-- For `X 1 - X 0 - 1` and `I = {1}`, three pairs with distinct coordinates are counted, and
`3 * (3 - 1) = (X 1 - X 0 - 1).degreeOf 1 * (#univ).descFactorial 2`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ ∀ i ∈ ({1} : Finset (Fin 2)),
        aeval (fun j ↦ if j < i then C (x j) else X j)
          (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 ∧
        aeval (fun j ↦ if j ≤ i then C (x j) else X j)
          (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} *
        ∏ i ∈ ({1} : Finset (Fin 2)), (#(univ : Finset (ZMod 3)) - i) =
      (∏ i ∈ ({1} : Finset (Fin 2)), (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)).degreeOf i) *
        (#(univ : Finset (ZMod 3))).descFactorial 2 := by
  have hP : ∀ x : Fin 2 → ZMod 3, (∀ i ∈ ({1} : Finset (Fin 2)),
      aeval (fun j ↦ if j < i then C (x j) else X j)
        (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 ∧
      aeval (fun j ↦ if j ≤ i then C (x j) else X j)
        (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0) ↔ x 1 - x 0 - 1 = 0 := by
    intro x
    have h1 : aeval (fun j : Fin 2 ↦ if j < 1 then C (x j) else X j)
        (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = X 1 - C (x 0) - 1 := by
      simp
    have h2 : aeval (fun j : Fin 2 ↦ if j ≤ 1 then C (x j) else X j)
        (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = C (x 1 - x 0 - 1) := by
      simp
    simp only [mem_singleton, forall_eq, h1, h2, C_eq_zero]
    exact and_iff_right (X_one_sub_C_sub_one_ne_zero _)
  have hcount : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ ∀ i ∈ ({1} : Finset (Fin 2)),
        aeval (fun j ↦ if j < i then C (x j) else X j)
          (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 ∧
        aeval (fun j ↦ if j ≤ i then C (x j) else X j)
          (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} = 3 := by
    rw [filter_congr fun x _ ↦ and_congr Iff.rfl (hP x)]
    decide
  rw [hcount, prod_singleton, prod_singleton, degreeOf_X_one_sub_X_zero_sub_one, card_univ,
    ZMod.card]
  rfl

/-- For `X 0 * X 1` and `I = {1}`, two pairs with distinct coordinates are counted, while
`X 0 * X 1` vanishes at four of them. Counting all four would give `4 * (3 - 1) = 8 > 6 = 1 * 6`,
so the bound needs the condition that `X 0 * X 1` is nonzero after substituting `x 0`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ ∀ i ∈ ({1} : Finset (Fin 2)),
        aeval (fun j ↦ if j < i then C (x j) else X j)
          (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 ∧
        aeval (fun j ↦ if j ≤ i then C (x j) else X j)
          (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} = 2 ∧
    #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ eval x (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} = 4 := by
  have hP : ∀ x : Fin 2 → ZMod 3, (∀ i ∈ ({1} : Finset (Fin 2)),
      aeval (fun j ↦ if j < i then C (x j) else X j)
        (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 ∧
      aeval (fun j ↦ if j ≤ i then C (x j) else X j)
        (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0) ↔ x 0 ≠ 0 ∧ x 0 * x 1 = 0 := by
    intro x
    have h1 : aeval (fun j : Fin 2 ↦ if j < 1 then C (x j) else X j)
        (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = C (x 0) * X 1 := by
      simp
    have h2 : aeval (fun j : Fin 2 ↦ if j ≤ 1 then C (x j) else X j)
        (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = C (x 0 * x 1) := by
      simp
    simp only [mem_singleton, forall_eq, h1, h2, C_eq_zero, ne_eq, mul_eq_zero, X_ne_zero,
      or_false]
  refine ⟨?_, ?_⟩
  · rw [filter_congr fun x _ ↦ and_congr Iff.rfl (hP x)]
    decide
  · simp only [map_mul, eval_X]
    decide

/-- For `P 0 = X 0`, `P 1 = X 1 - X 0 - 1` and `I = {0, 1}`, only `(0, 1)` is counted, and
`1 * ((3 - 0) * (3 - 1)) = ((X 0).degreeOf 0 * (X 1 - X 0 - 1).degreeOf 1) * 6`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ ∀ i ∈ ({0, 1} : Finset (Fin 2)),
        aeval (fun j ↦ if j < i then C (x j) else X j)
          ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i) ≠ 0 ∧
        aeval (fun j ↦ if j ≤ i then C (x j) else X j)
          ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i) = 0} *
        ∏ i ∈ ({0, 1} : Finset (Fin 2)), (#(univ : Finset (ZMod 3)) - i) =
      (∏ i ∈ ({0, 1} : Finset (Fin 2)),
        ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i).degreeOf i) *
        (#(univ : Finset (ZMod 3))).descFactorial 2 := by
  have hP : ∀ x : Fin 2 → ZMod 3, (∀ i ∈ ({0, 1} : Finset (Fin 2)),
      aeval (fun j ↦ if j < i then C (x j) else X j)
        ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i) ≠ 0 ∧
      aeval (fun j ↦ if j ≤ i then C (x j) else X j)
        ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i) = 0) ↔
      x 0 = 0 ∧ x 1 - x 0 - 1 = 0 := by
    intro x
    have h0 : aeval (fun j : Fin 2 ↦ if j < 0 then C (x j) else X j)
        (X 0 : MvPolynomial (Fin 2) (ZMod 3)) = X 0 := by
      simp
    have h0' : aeval (fun j : Fin 2 ↦ if j ≤ 0 then C (x j) else X j)
        (X 0 : MvPolynomial (Fin 2) (ZMod 3)) = C (x 0) := by
      simp
    have h1 : aeval (fun j : Fin 2 ↦ if j < 1 then C (x j) else X j)
        (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = X 1 - C (x 0) - 1 := by
      simp
    have h1' : aeval (fun j : Fin 2 ↦ if j ≤ 1 then C (x j) else X j)
        (X 1 - X 0 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = C (x 1 - x 0 - 1) := by
      simp
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, h0, h0', h1, h1', C_eq_zero, ne_eq, X_ne_zero,
      X_one_sub_C_sub_one_ne_zero, not_false_eq_true, true_and]
  have hcount : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ ∀ i ∈ ({0, 1} : Finset (Fin 2)),
        aeval (fun j ↦ if j < i then C (x j) else X j)
          ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i) ≠ 0 ∧
        aeval (fun j ↦ if j ≤ i then C (x j) else X j)
          ((![X 0, X 1 - X 0 - 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 3)) i) = 0} = 1 := by
    rw [filter_congr fun x _ ↦ and_congr Iff.rfl (hP x)]
    decide
  rw [hcount, prod_pair (by decide), prod_pair (by decide), card_univ, ZMod.card]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, degreeOf_X_self,
    degreeOf_X_one_sub_X_zero_sub_one]
  rfl
