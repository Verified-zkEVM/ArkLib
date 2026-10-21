/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.PDeriv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Partial-derivative degree acceptance tests

These examples separate characteristic zero from positive characteristic. In `ZMod 2` the
derivative of `X² ` vanishes, so exact degree loss needs the cast hypothesis, while over `ℚ` the
cast hypothesis holds and the exact theorems apply. Further examples show that `NoZeroDivisors`
is needed (`ZMod 4`), that the iterated cast hypothesis allows degrees at or above the
characteristic, and that iterated nonvanishing needs `p ≠ 0` at order zero.
-/

open MvPolynomial

/-! ### One derivative -/

/-- In characteristic two, `∂(X²) = 2X = 0`, so the degree drops by two rather than one. The cast
hypothesis `((2 : ℕ) : ZMod 2) ≠ 0` fails, as it must. -/
example :
    pderiv 0 (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) = 0 ∧
      degreeOf 0 (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) = 2 ∧
      ((degreeOf 0 (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) : ℕ) : ZMod 2) = 0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  refine ⟨?_, degreeOf_X_self_pow 0 2, ?_⟩
  · rw [pderiv_pow, pderiv_X_self, mul_one]
    change C ((2 : ℕ) : ZMod 2) * X 0 ^ 1 = 0
    rw [ZMod.natCast_self, C_0, zero_mul]
  · rw [degreeOf_X_self_pow]
    exact ZMod.natCast_self 2

/-- Over `ℚ` (characteristic zero) the same polynomial keeps a nonzero derivative, and `∂(X³)` has
degree exactly two. -/
example :
    pderiv 0 (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧
      degreeOf 0 (pderiv 0 (X 0 ^ 3 : MvPolynomial (Fin 1) ℚ)) = 2 := by
  constructor
  · apply pderiv_ne_zero_of_natCast_ne_zero
    rw [degreeOf_X_self_pow]
    norm_num
  · rw [degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero, degreeOf_X_self_pow]
    rw [degreeOf_X_self_pow]
    norm_num

/-- `NoZeroDivisors` is needed: over `ZMod 4`, `2X²` has degree `2` and `(2 : ZMod 4) ≠ 0`, yet
its derivative `4X` is zero. -/
example :
    let p : MvPolynomial (Fin 1) (ZMod 4) := C 2 * X 0 ^ 2
    degreeOf 0 p = 2 ∧ ((degreeOf 0 p : ℕ) : ZMod 4) ≠ 0 ∧ pderiv 0 p = 0 := by
  dsimp only
  have hmon : (C 2 * X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 4)) =
      monomial (Finsupp.single 0 2) 2 := by
    rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
  have hdeg : degreeOf 0 (C 2 * X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 4)) = 2 := by
    rw [hmon, degreeOf_monomial_eq _ _ (by decide), Finsupp.single_eq_same]
  refine ⟨hdeg, by rw [hdeg]; decide, ?_⟩
  rw [pderiv_C_mul, pderiv_pow, pderiv_X_self, mul_one, ← mul_assoc, ← C_eq_coe_nat, ← C_mul]
  have hfour : (2 : ZMod 4) * ((2 : ℕ) : ZMod 4) = 0 := by decide
  rw [hfour, C_0, zero_mul]

/-- Partial differentiation in `X 0` does not raise the degree in `X 1`, and here preserves it. -/
example :
    degreeOf 1 (pderiv 0 (X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 2) ℚ)) ≤ 3 := by
  refine (degreeOf_pderiv_le 0 1 _).trans ?_
  refine (degreeOf_mul_le 1 _ _).trans ?_
  rw [degreeOf_X_self_pow, X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  simp

/-! ### Characteristic guard -/

/-- `ZMod 5` is a field, so it has no zero divisors. -/
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- In `ZMod 5` the guard `4 < ringChar` gives the casts of `1, …, 4`. -/
example (k : ℕ) (hk : 0 < k) (hk4 : k ≤ 4) : (k : ZMod 5) ≠ 0 :=
  natCast_ne_zero_of_ringChar_eq_zero_or_lt (n := 4)
    (Or.inr (by rw [ZMod.ringChar_zmod_n]; norm_num)) hk hk4

/-- In characteristic zero the guard holds for every bound, through the `ringChar R = 0`
disjunct. -/
example (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : (k : ℚ) ≠ 0 :=
  natCast_ne_zero_of_ringChar_eq_zero_or_lt (Or.inl (ringChar.eq_zero (R := ℚ))) hk hkn

/-! ### Iterated derivatives -/

/-- In `ZMod 5`, differentiating `X⁴` four times gives the nonzero constant `4! = 24 = 4`: the
cast hypothesis is discharged by the characteristic guard. -/
example :
    (pderiv 0)^[4] (X 0 ^ 4 : MvPolynomial (Fin 1) (ZMod 5)) ≠ 0 ∧
      degreeOf 0 ((pderiv 0)^[4] (X 0 ^ 4 : MvPolynomial (Fin 1) (ZMod 5))) = 0 := by
  have hcast : ∀ k < 4,
      ((degreeOf 0 (X 0 ^ 4 : MvPolynomial (Fin 1) (ZMod 5)) - k : ℕ) : ZMod 5) ≠ 0 := by
    intro k hk
    rw [degreeOf_X_self_pow]
    exact natCast_ne_zero_of_ringChar_eq_zero_or_lt (n := 4)
      (Or.inr (by rw [ZMod.ringChar_zmod_n]; norm_num)) (by omega) (by omega)
  refine ⟨iterate_pderiv_ne_zero_of_natCast_ne_zero 0 4 (pow_ne_zero 4 (X_ne_zero 0)) hcast, ?_⟩
  rw [degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero 0 4 _ hcast, degreeOf_X_self_pow]

/-- The iterated cast hypothesis concerns only the differentiated degrees, so it can hold at or
above the characteristic: in `ZMod 5`, one derivative of `X⁶` has degree `5`, because
`(6 : ZMod 5) = 1`. A hypothesis `degreeOf 0 p < ringChar (ZMod 5)` would exclude this. -/
example :
    degreeOf 0 ((pderiv 0)^[1] (X 0 ^ 6 : MvPolynomial (Fin 1) (ZMod 5))) = 5 := by
  rw [degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero, degreeOf_X_self_pow]
  intro k hk
  rw [degreeOf_X_self_pow]
  obtain rfl : k = 0 := by omega
  decide

/-- The characteristic obstruction for iterates: in `ZMod 5`, one derivative of `X⁵` is zero,
and the cast hypothesis fails at `k = 0`. -/
example :
    (pderiv 0)^[1] (X 0 ^ 5 : MvPolynomial (Fin 1) (ZMod 5)) = 0 ∧
      ((degreeOf 0 (X 0 ^ 5 : MvPolynomial (Fin 1) (ZMod 5)) - 0 : ℕ) : ZMod 5) = 0 := by
  constructor
  · rw [Function.iterate_one, pderiv_pow, pderiv_X_self, mul_one, ← C_eq_coe_nat,
      ZMod.natCast_self, C_0, zero_mul]
  · rw [degreeOf_X_self_pow]
    exact ZMod.natCast_self 5

/-- Nonvanishing of iterates needs `p ≠ 0` at order zero: for `p = 0` and `a = 0` the cast
hypothesis is vacuous and the degree equality holds, but the iterate is zero. -/
example :
    (∀ k < 0, ((degreeOf 0 (0 : MvPolynomial (Fin 1) ℚ) - k : ℕ) : ℚ) ≠ 0) ∧
      degreeOf 0 ((pderiv 0)^[0] (0 : MvPolynomial (Fin 1) ℚ)) =
        degreeOf 0 (0 : MvPolynomial (Fin 1) ℚ) - 0 ∧
      (pderiv 0)^[0] (0 : MvPolynomial (Fin 1) ℚ) = 0 :=
  ⟨fun k hk => absurd hk (Nat.not_lt_zero k), rfl, rfl⟩

/-- Differentiating past the degree gives zero in every characteristic, here over `ℚ`. -/
example : (pderiv 0)^[3] (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) = 0 :=
  iterate_pderiv_eq_zero_of_degreeOf_lt (by rw [degreeOf_X_self_pow]; norm_num)
