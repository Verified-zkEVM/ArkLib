/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldResultant
import ArkLib.Data.Polynomial.ResultantSpecialization
import Mathlib.Algebra.Field.ZMod

/-! Declared-degree resultants under specialization: the nonmonic linear polynomial `X * Y + 1`,
a derivative whose degree drops in characteristic two, a Bezout divisibility certificate over `ℤ`,
and the `m = n = 0` boundary. -/

open Polynomial

namespace ResultantSpecializationTest

section Canary

variable {F : Type*} [Field F]

/-- The nonmonic linear polynomial `A = X * Y + 1`, with `Y` the outer variable. -/
noncomputable def canary : F[X][X] := C X * X + C 1

theorem canary_natDegree : (canary : F[X][X]).natDegree = 1 :=
  natDegree_linear X_ne_zero

theorem canary_derivative : (canary : F[X][X]).derivative = C X := by
  simp [canary]

example : ¬(canary : F[X][X]).Monic := by
  rw [Monic, canary, leadingCoeff_linear X_ne_zero]
  exact fun h ↦ X_ne_C (1 : F) (by simpa using h)

-- With declared degree 1, the padded derivative resultant `resultant A A.derivative 1 0` is
-- exactly `X`. The reversed order `resultant A.derivative A 0 1` gives the same value, with no
-- sign, because `1 * 0` is even.
theorem canary_resultant : resultant (canary : F[X][X]) canary.derivative 1 0 = X := by
  simp [canary_derivative]

example : resultant (canary : F[X][X]).derivative canary 0 1 = X := by
  rw [show (0 : ℕ) = 1 - 1 from rfl, resultant_comm_sub_one, canary_resultant]

example : (resultant (canary : F[X][X]) canary.derivative 1 0).natDegree = 1 := by
  rw [canary_resultant, natDegree_X]

-- Away from `X = 0`, every specialization of the canary is separable and keeps degree 1.
example (t : F) (ht : t ≠ 0) : ((canary : F[X][X]).map (evalRingHom t)).Separable := by
  refine separable_map_of_resultant_derivative_padded_ne_zero (evalRingHom t) canary
    canary_natDegree.le Nat.one_pos ?_
  rwa [Nat.sub_self, canary_resultant, coe_evalRingHom, eval_X]

example (t : F) (ht : t ≠ 0) : ((canary : F[X][X]).map (evalRingHom t)).natDegree = 1 := by
  refine natDegree_map_eq_of_resultant_derivative_padded_ne_zero (evalRingHom t) canary
    canary_natDegree.le Nat.one_pos ?_
  rwa [Nat.sub_self, canary_resultant, coe_evalRingHom, eval_X]

-- At `X = 0` the canary drops to the constant `1`; the degree lemma forces the padded derivative
-- resultant to vanish there.
example : evalRingHom (0 : F) (resultant (canary : F[X][X]) canary.derivative 1 0) = 0 := by
  by_contra hres
  have hdegree := natDegree_map_eq_of_resultant_derivative_padded_ne_zero (evalRingHom (0 : F))
    canary canary_natDegree.le Nat.one_pos hres
  simp [canary] at hdegree

-- The regular-root corollary at the concrete root `-1 / t` of `t * Y + 1`.
example (t : F) (ht : t ≠ 0) :
    ((canary : F[X][X]).map (evalRingHom t)).derivative.eval (-1 / t) ≠ 0 := by
  refine eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (evalRingHom t)
    canary canary_natDegree.le Nat.one_pos ?_ _ ?_
  · rwa [Nat.sub_self, canary_resultant, coe_evalRingHom, eval_X]
  · simp [canary, mul_div_cancel₀ _ ht]

end Canary

section SmallCharacteristic

/-- `Y ^ 2 + Y` over `ℤ`. Its derivative `2 * Y + 1` has degree `1 = m - 1` for `m = 2`. -/
noncomputable def quadratic : ℤ[X] := X ^ 2 + X

theorem quadratic_natDegree : quadratic.natDegree = 2 := by
  rw [quadratic, natDegree_add_eq_left_of_natDegree_lt] <;> simp

-- Reducing modulo 2 lowers the degree of the derivative from `1` to `0`.
theorem quadratic_map_derivative :
    (quadratic.map (Int.castRingHom (ZMod 2))).derivative = 1 := by
  simp [quadratic, one_add_one_eq_two, CharTwo.two_eq_zero]

example : quadratic.derivative.natDegree = 1 ∧
    (quadratic.map (Int.castRingHom (ZMod 2))).derivative.natDegree < 2 - 1 := by
  refine ⟨?_, by rw [quadratic_map_derivative, natDegree_one]; norm_num⟩
  have hderivative : quadratic.derivative = C 2 * X + C 1 := by
    simp [quadratic]
  rw [hderivative, natDegree_linear (by norm_num)]

-- The declared-degree resultant still survives the reduction: it maps to `1`.
theorem quadratic_resultant_map :
    Int.castRingHom (ZMod 2) (resultant quadratic quadratic.derivative 2 1) = 1 := by
  rw [← resultant_map_map, ← derivative_map, quadratic_map_derivative, resultant_one_right]
  simp [quadratic, coeff_X]

example : (quadratic.map (Int.castRingHom (ZMod 2))).Separable :=
  separable_map_of_resultant_derivative_padded_ne_zero _ quadratic quadratic_natDegree.le
    two_pos (by rw [quadratic_resultant_map]; exact one_ne_zero)

example : (quadratic.map (Int.castRingHom (ZMod 2))).derivative.eval 1 ≠ 0 := by
  refine eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero _ quadratic
    quadratic_natDegree.le two_pos (by rw [quadratic_resultant_map]; exact one_ne_zero) 1 ?_
  simp [quadratic, one_add_one_eq_two, CharTwo.two_eq_zero]

example : (quadratic.map (Int.castRingHom (ZMod 2))).natDegree = 2 :=
  natDegree_map_eq_of_resultant_derivative_padded_ne_zero _ quadratic quadratic_natDegree.le
    two_pos (by rw [quadratic_resultant_map]; exact one_ne_zero)

/-- `T * Y ^ 2 + Y` over `(ZMod 2)[T]`. Its derivative is `1`, so the derivative's degree is
already below `m - 1 = 1` before specialization. -/
noncomputable def dropping : (ZMod 2)[X][X] := C X * X ^ 2 + X

theorem dropping_derivative : dropping.derivative = 1 := by
  simp [dropping, one_add_one_eq_two, CharTwo.two_eq_zero]

-- At `T = 0` the degree of `dropping` itself drops from 2 to 1. The actual-degree derivative
-- resultant `resultant f f.derivative 2 0 = 1` still certifies separability, but the padded one
-- with declared degrees `2, 1` equals the leading coefficient `T` and vanishes at `T = 0`.
example : (dropping.map (evalRingHom (0 : ZMod 2))).Separable := by
  refine separable_map_of_resultant_derivative_ne_zero _ dropping ?_ ?_
  · rw [dropping, natDegree_add_eq_left_of_natDegree_lt] <;> simp
  · rw [dropping_derivative, resultant_one_right]
    simp

example : evalRingHom (0 : ZMod 2) (resultant dropping dropping.derivative 2 1) = 0 := by
  rw [dropping_derivative, resultant_one_right]
  simp [dropping, coeff_X]

end SmallCharacteristic

section CommonRoot

-- The Bezout certificate over `ℤ` gives a divisibility without computing the resultant:
-- `Y ^ 2 + 1` and `Y + 3` share the root `2` modulo `5`.
example : (5 : ℤ) ∣ resultant (X ^ 2 + 1 : ℤ[X]) (X + 3) 2 1 := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp ?_
  refine map_resultant_eq_zero_of_common_root (Int.castRingHom (ZMod 5)) _ _ ?_ ?_
    (Or.inl two_ne_zero) 2 ?_ ?_
  · exact (natDegree_add_le _ _).trans (by simp)
  · exact (natDegree_add_le _ _).trans (by simp)
  · simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one, eval_add,
      eval_pow, eval_X, eval_one]
    decide
  · simp only [Polynomial.map_add, map_X, Polynomial.map_ofNat, eval_add, eval_X, eval_ofNat]
    decide

-- With `m = n = 0` the resultant is `1` although `0` and `0` share every root, so the hypothesis
-- `m ≠ 0 ∨ n ≠ 0` of `map_resultant_eq_zero_of_common_root` cannot be dropped.
example : resultant (0 : ℚ[X]) 0 0 0 = 1 ∧ ((0 : ℚ[X]).map (RingHom.id ℚ)).eval 0 = 0 := by
  simp

end CommonRoot

end ResultantSpecializationTest
