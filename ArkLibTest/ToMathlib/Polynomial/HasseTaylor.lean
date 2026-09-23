/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! # Hasse--Taylor acceptance tests -/

namespace Polynomial

example : hasseCoeffAt (1 : ℚ) 2 (hassePerturbation 1 3 2) = 3 := by
  simpa using hasseCoeffAt_hassePerturbation (1 : ℚ) 3 2 2

example : hasseDeriv 1 (hassePerturbation (1 : ℚ) 3 2) = hassePerturbation 1 6 1 := by
  rw [hasseDeriv_hassePerturbation]
  norm_num

example :
    hasseCoeffAt (0 : ℚ) 1
        (hasseDeriv 1 (0 + hassePerturbation 0 3 2)) = 6 ∧
      hasseCoeffAt (0 : ℚ) 0
        (hasseDeriv 1 (0 + hassePerturbation 0 3 2)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation
      (p := (0 : ℚ[X])) (a := 0) (γ := 3) (i := 2) (s := 1)]
    norm_num
  · rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt
      (p := (0 : ℚ[X])) (a := 0) (γ := 3) (i := 2) (j := 0) (s := 1) (by norm_num)]
    simp

example :
    ∃! γ : ℚ,
      hasseCoeffAt (1 : ℚ) 1
        (hasseDeriv 1 (0 + hassePerturbation 1 γ 2)) = 6 :=
  existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq
    (0 : ℚ[X]) 1 6 (i := 2) (s := 1) (by norm_num)

example : ((Nat.choose 4 2 : ℕ) : ZMod 5) ≠ 0 :=
  natCast_choose_ne_zero_of_lt_charP Nat.prime_five (by norm_num) (by norm_num)

example :
    X ∣ taylor (1 : ℚ) (X - C 1 : ℚ[X]) ↔ (X - C 1 : ℚ[X]) ∣ X - C 1 :=
  by
    simpa only [pow_one] using X_pow_dvd_taylor_iff_X_sub_C_pow_dvd (X - C 1 : ℚ[X]) 1 1

example :
    X ^ 1 ∣ taylor (0 : ℚ) (hasseDeriv 1 (X ^ 2 : ℚ[X])) -
      taylor (0 : ℚ) (hasseDeriv 1 (0 : ℚ[X])) := by
  have hdiv : X ^ 2 ∣ taylor (0 : ℚ) (X ^ 2 : ℚ[X]) - taylor 0 0 := by
    refine ⟨1, ?_⟩
    simp
  have h := X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd
    (p := (X ^ 2 : ℚ[X])) (q := 0) (a := 0) (m := 1) (s := 1) hdiv
  exact h

example :
    X ^ (2 + 1) ∣ (X ^ 2 + X ^ 3 : ℚ[X]) ↔
      (X ^ 2 + X ^ 3 : ℚ[X]).coeff 2 = 0 :=
  X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd
    (p := (X ^ 2 + X ^ 3 : ℚ[X])) (k := 2)
    (by refine ⟨1 + X, ?_⟩; ring)

end Polynomial
