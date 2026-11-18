/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.RingTheory.PowerSeries.SimpleRoot

/-! # Acceptance cases for power series roots over a simple root -/

open PowerSeries

/-- The Catalan equation `X U² - U + 1` over `ℤ⟦X⟧`, which is not monic. -/
private noncomputable def catalan : Polynomial (PowerSeries ℤ) :=
  Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1

-- Over `ℤ`, the simple root `1` of `-U + 1` lifts to a unique series root.
example : ∃! E : PowerSeries ℤ, constantCoeff E = 1 ∧ catalan.eval E = 0 :=
  existsUnique_constantCoeff_eq_and_eval_eq_zero catalan 1 (by simp [catalan])
    (by simp [catalan])

-- The coefficient of `X` in the Catalan root is the Catalan number `1`.
example (E : PowerSeries ℤ) (hE0 : constantCoeff E = 1) (hE : catalan.eval E = 0) :
    coeff 1 E = 1 := by
  have h := congrArg (coeff 1) hE
  simp [catalan, pow_two, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hE0] at h
  linarith

-- Without a unit derivative, uniqueness fails: `U² - X²` has the roots `±X`.
example : ¬ ∃! E : PowerSeries ℚ, constantCoeff E = 0 ∧
    (Polynomial.X ^ 2 - Polynomial.C (X ^ 2) : Polynomial (PowerSeries ℚ)).eval E = 0 := by
  rintro ⟨E, -, huniq⟩
  have h₁ := huniq X ⟨by simp, by simp⟩
  have h₂ := huniq (-X) ⟨by simp, by simp⟩
  have h := congrArg (coeff 1) (h₁.trans h₂.symm)
  norm_num at h

-- The truncation of the root `X` of `U - X` below degree `2` is a root up to `X¹`.
example : coeff 1 ((Polynomial.X - Polynomial.C X : Polynomial (PowerSeries ℚ)).eval
    ((trunc 2 X : Polynomial ℚ) : PowerSeries ℚ)) = 0 :=
  coeff_eval_trunc_eq_zero (by simp) (by norm_num)

/--
info: 'PowerSeries.existsUnique_constantCoeff_eq_and_eval_eq_zero' depends on axioms: [propext,
 Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PowerSeries.existsUnique_constantCoeff_eq_and_eval_eq_zero
