/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.ShiftedJet

/-!
# Shifted-jet substitution acceptance tests

For `P = X²` at center `a`, the shifted-jet substitution sends `Y₀` to `(a + X)²` and `Y₁` to
`2(a + X)`, and `Y₀ - X Y₁` to `(a + X)² - 2X(a + X)`. The identity with Taylor translation is
checked over `ℕ`, a semiring that is not a ring, and at `d = 0`, where the only jet is `Y₀`.
-/

open Polynomial PolynomialDifferential

/-- `Y₀` goes to `(a + X)²` when `P = X²`. -/
example (a : ℚ) :
    shiftedJetSubstitution (d := 1) a (X ^ 2) (MvPolynomial.X (some 0)) = (C a + X) ^ 2 := by
  rw [shiftedJetSubstitution_Y_zero, taylor_pow, taylor_X, add_comm]

/-- `Y₁` goes to the translate of `D¹(X²) = 2X`. -/
example (a : ℚ) :
    shiftedJetSubstitution (d := 1) a (X ^ 2) (MvPolynomial.X (some 1)) = 2 * (C a + X) := by
  have h := shiftedJetSubstitution_Y_succ (d := 1) a (X ^ 2 : ℚ[X]) 0
  simp only [Fin.succ_zero_eq_one, Fin.val_zero, zero_add, hasseDeriv_one] at h
  rw [h, derivative_X_pow]
  simp only [taylor_apply, add_comm]
  simp [C_ofNat]

/-- The shifted-jet image of `Y₀ - X Y₁` at `P = X²`, computed from the Taylor identity. -/
example (a : ℚ) :
    shiftedJetSubstitution (d := 1) a (X ^ 2)
        (MvPolynomial.X (some 0) - MvPolynomial.X none * MvPolynomial.X (some 1)) =
      taylor a (X ^ 2 - X * derivative (X ^ 2)) := by
  rw [← taylor_differentialSpecialization]
  simp only [differentialSpecialization, map_sub, map_mul]
  simp [hasseDeriv_one]

/-- Over the semiring `ℕ` at `d = 0`: the substitution of `X · Y₀` is `taylor a (X · P)`. -/
example (a : ℕ) (P : ℕ[X]) :
    shiftedJetSubstitution (d := 0) a P (MvPolynomial.X none * MvPolynomial.X (some 0)) =
      taylor a (X * P) := by
  rw [← taylor_differentialSpecialization]
  simp only [differentialSpecialization, map_mul]
  simp
