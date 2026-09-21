/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.CompleteHomogeneous
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Acceptance cases for complete homogeneous symmetric polynomials

Concrete evaluations of `hsymm` in degrees `2` and `3` obtained from the Newton identities, a
case over the semiring `ℕ`, where the factors `2` and `6` cannot be divided out, the empty index
type, and the exponent-vector form on a single variable.
-/

open MvPolynomial Finset

/-- `h₂(1, 2) = 1 + 2 + 4 = 7`, from `2 * h₂ = 3 ^ 2 + 5`. -/
example : eval (![1, 2] : Fin 2 → ℝ) (hsymm (Fin 2) ℝ 2) = 7 := by
  have h := two_mul_eval_hsymm_two (![1, 2] : Fin 2 → ℝ)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  linarith

/-- `h₃(1, 1) = 4`: the monomials `x³, x²y, xy², y³`. From `6 * h₃ = 8 + 3 * 2 * 2 + 2 * 2`. -/
example : eval (fun _ : Fin 2 ↦ (1 : ℝ)) (hsymm (Fin 2) ℝ 3) = 4 := by
  have h := six_mul_eval_hsymm_three (fun _ : Fin 2 ↦ (1 : ℝ))
  norm_num at h
  linarith

/-- Over the semiring `ℕ`: `h₂(1, 2, 3) = 25`, from `2 * h₂ = 6 ^ 2 + 14`. -/
example : 2 * eval (![1, 2, 3] : Fin 3 → ℕ) (hsymm (Fin 3) ℕ 2) = 50 := by
  rw [two_mul_eval_hsymm_two]
  simp [Fin.sum_univ_three]

/-- With no variables every positive-degree complete homogeneous polynomial vanishes. -/
example (c : Fin 0 → ℝ) : eval c (hsymm (Fin 0) ℝ 3) = 0 := by
  simpa using six_mul_eval_hsymm_three c

/-- In one variable, `h_k(x) = x ^ k`: the only exponent vector is `![k]`. -/
example (x : ℝ) (k : ℕ) : eval (fun _ : Fin 1 ↦ x) (hsymm (Fin 1) ℝ k) = x ^ k := by
  rw [eval_hsymm_eq_sum_piAntidiag, piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple_one]
  simp
