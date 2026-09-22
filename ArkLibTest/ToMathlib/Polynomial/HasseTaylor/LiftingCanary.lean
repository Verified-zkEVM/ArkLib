/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Canaries for centered Hasse perturbations

* Over `ℚ`, the first Hasse derivative of `3 (X - 1)²` is `6 (X - 1)`, and a unique
  perturbation coefficient reaches any prescribed value.
* Over `ℤ`, with `i = 2` and `s = 1`, the coefficient moves by `2 γ`, so the value `1` is never
  reached: the unit hypothesis of the existence statement is needed.
* Over `ZMod 2`, `(2 choose 1) = 0`, so the perturbation coefficient is not determined: the
  regularity hypothesis of the injectivity statement is needed.
* In `ZMod 5`, `(4 choose 2) ≠ 0` follows from the prime-characteristic bound, while
  `(5 choose 1) = 0` shows that the bound `i < p` is needed.
-/

namespace Polynomial

/-- The first Hasse derivative of `3 (X - 1)²` is `6 (X - 1)`. -/
example : hasseDeriv 1 (hassePerturbation (1 : ℚ) 3 2) = hassePerturbation 1 6 1 := by
  rw [hasseDeriv_hassePerturbation]
  norm_num

/-- A perturbation of order two leaves the length-two jet unchanged. -/
example (p : ℚ[X]) (γ : ℚ) :
    hasseJet 2 (1 : ℚ) (p + hassePerturbation 1 γ 2) = hasseJet 2 1 p :=
  hasseJet_add_hassePerturbation_of_le p 1 γ le_rfl

/-- Over `ℚ`, `(2 choose 1) = 2` is a unit, so exactly one `γ` gives coefficient `5`. -/
example (p : ℚ[X]) :
    ∃! γ : ℚ, hasseCoeffAt (1 : ℚ) (2 - 1) (hasseDeriv 1 (p + hassePerturbation 1 γ 2)) = 5 :=
  existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq p 1 5
    (by norm_num : IsUnit ((Nat.choose 2 1 : ℕ) : ℚ))

/-- Over `ℤ`, the coefficient moves by `2 γ` and never reaches `1`. -/
example : ¬∃ γ : ℤ,
    hasseCoeffAt (0 : ℤ) (2 - 1) (hasseDeriv 1 (0 + hassePerturbation 0 γ 2)) = 1 := by
  rintro ⟨γ, hγ⟩
  rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation] at hγ
  simp only [map_zero, zero_add, Nat.choose_one_right, Nat.cast_ofNat] at hγ
  omega

/-- Over `ZMod 2`, `(2 choose 1) = 0`, so the perturbation coefficient is not determined. -/
example : ¬Function.Injective fun γ : ZMod 2 ↦
    hasseCoeffAt (0 : ZMod 2) (2 - 1) (hasseDeriv 1 (0 + hassePerturbation 0 γ 2)) := by
  intro h
  have h01 : (0 : ZMod 2) = 1 := h (by
    have htwo : ((Nat.choose 2 1 : ℕ) : ZMod 2) = 0 := by decide
    simp only [hasseCoeffAt_hasseDeriv_add_hassePerturbation, htwo, zero_mul])
  exact absurd h01 (by decide)

/-- In characteristic `5`, `(4 choose 2)` is nonzero. -/
example : ((Nat.choose 4 2 : ℕ) : ZMod 5) ≠ 0 :=
  natCast_choose_ne_zero_of_lt_charP Nat.prime_five (by norm_num) (by norm_num)

/-- The bound `i < p` is needed: `(5 choose 1)` vanishes in characteristic `5`. -/
example : ((Nat.choose 5 1 : ℕ) : ZMod 5) = 0 := by
  decide

/-- Divisibility by `X ^ 2` of `X ^ 2 + X ^ 3` upgrades to `X ^ 3` exactly when the coefficient
of `X ^ 2` vanishes, which it does not. -/
example : ¬(X : ℚ[X]) ^ 3 ∣ X ^ 2 + X ^ 3 := by
  rw [X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd (Dvd.intro (1 + X) (by ring))]
  simp [coeff_X_pow]

end Polynomial
