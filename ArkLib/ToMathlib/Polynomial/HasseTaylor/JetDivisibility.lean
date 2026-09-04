/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift

/-!
# Finite Hasse jets and polynomial divisibility

This file joins the finite-vector interface `hasseJet` with the scalar Hasse-vanishing and
divisibility results from `HasseTaylor.Shift`.  It lets downstream constraint maps use equality in
`Fin m → R` directly, while retaining the characteristic-independent meaning of the coordinates.
-/

namespace Polynomial

noncomputable section

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- A Taylor shift is divisible by `X ^ m` exactly when its length-`m` Hasse jet is zero. -/
theorem X_pow_dvd_taylor_iff_hasseJet_eq_zero (p : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p ↔ hasseJet m a p = 0 := by
  rw [X_pow_dvd_taylor_iff]
  constructor
  · intro h
    funext i
    simpa using h i i.isLt
  · intro h i hi
    have hi := congrFun h ⟨i, hi⟩
    simpa using hi

end Semiring

section CommRing

variable [CommRing R]

/-- A root has multiplicity at least `m` exactly when its length-`m` Hasse jet vanishes. -/
theorem X_sub_C_pow_dvd_iff_hasseJet_eq_zero (p : R[X]) (a : R) (m : ℕ) :
    (X - C a) ^ m ∣ p ↔ hasseJet m a p = 0 := by
  rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  constructor
  · intro h
    funext i
    simpa using h i i.isLt
  · intro h i hi
    have hi := congrFun h ⟨i, hi⟩
    simpa using hi

/-- Two polynomials agree to Hasse order `< m` at `a` exactly when their shifted difference is
divisible by `X ^ m`. -/
theorem X_pow_dvd_taylor_sub_iff_hasseJet_eq (p q : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p - taylor a q ↔ hasseJet m a p = hasseJet m a q := by
  rw [X_pow_dvd_taylor_sub_iff]
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

/-- Two polynomials have the same length-`m` Hasse jet at `a` exactly when their difference is
divisible by the `m`-th power of the corresponding root factor. -/
theorem X_sub_C_pow_dvd_sub_iff_hasseJet_eq (p q : R[X]) (a : R) (m : ℕ) :
    (X - C a) ^ m ∣ p - q ↔ hasseJet m a p = hasseJet m a q := by
  rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  constructor
  · intro h
    ext i
    simpa only [LinearMap.map_sub, eval_sub, sub_eq_zero, hasseJet_apply] using h i i.isLt
  · intro h i hi
    simpa only [LinearMap.map_sub, eval_sub, sub_eq_zero, hasseJet_apply] using
      congrFun h ⟨i, hi⟩

/-- For a nonzero polynomial, a zero finite Hasse jet is the corresponding root-multiplicity
lower bound. -/
theorem hasseJet_eq_zero_iff_le_rootMultiplicity {p : R[X]} (hp : p ≠ 0)
    (a : R) (m : ℕ) :
    hasseJet m a p = 0 ↔ m ≤ p.rootMultiplicity a := by
  rw [← X_sub_C_pow_dvd_iff_hasseJet_eq_zero]
  exact (le_rootMultiplicity_iff hp).symm

end CommRing

end

end Polynomial
