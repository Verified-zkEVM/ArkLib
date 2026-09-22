/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.LagrangeLine
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree

/-!
# Acceptance client for `ArkLib.ToMathlib.LinearAlgebra.LagrangeLine`

The examples map an interpolant from `ℚ` to `ℝ`, recognize the polynomial `1 + (1 + y) X` over
`ℝ` from its values at `0` and `1`, and show that recognition fails without the degree bound
(`X * (X - 1)`) and without injectivity of the nodes (`X` with both nodes at `0`). Over
`ZMod 2`, `X ^ 2 + 1` is recognized as a Frobenius pullback from two values, and `X ^ 3 - X`,
which is not sparse, shows that the sparsity hypothesis is needed.
-/

open Polynomial Finset Lagrange

namespace LagrangeLineTest

/-- The nodes `0, 1` over `ℚ`. -/
def v : Fin 2 → ℚ := ![0, 1]

lemma v_injOn : Set.InjOn v (univ : Finset (Fin 2)) := by
  intro i _ j _ h
  fin_cases i <;> fin_cases j <;> simp_all [v]

/-- The interpolant of the values `1, 2` at `0, 1` is `1 + X`. -/
lemma interpolate_line : interpolate univ v ![1, 2] = C 1 + X := by
  symm
  apply eq_interpolate_of_eval_eq _ v_injOn
  · rw [card_univ, Fintype.card_fin]
    compute_degree!
  · intro i _
    fin_cases i <;> norm_num [v]

/-- Mapping to `ℝ` commutes with interpolation. -/
example : (interpolate univ v ![1, 2]).map (Rat.castHom ℝ) =
    interpolate univ (Rat.castHom ℝ ∘ v) (Rat.castHom ℝ ∘ ![1, 2]) :=
  map_interpolate _ _ _ _

/-- Recognition over `ℝ`: `1 + (1 + y) X` takes the values `1 + y * 0` and `2 + y * 1` at `0`
and `1`, so it is `(1 + X) + C y * X`, computed from the two rational interpolants. -/
example (y : ℝ) : (C 1 + C (1 + y) * X : ℝ[X]) =
    (C 1 + X : ℚ[X]).map (Rat.castHom ℝ) + C y * (X : ℚ[X]).map (Rat.castHom ℝ) := by
  have hX : interpolate univ v ![0, 1] = X := by
    symm
    apply eq_interpolate_of_eval_eq _ v_injOn
    · rw [card_univ, Fintype.card_fin]
      compute_degree!
    · intro i _
      fin_cases i <;> simp [v]
  rw [← interpolate_line, ← hX]
  apply eq_map_interpolate_add_C_mul_of_eval_eq _ v_injOn
  · rw [card_univ, Fintype.card_fin]
    compute_degree!
  · intro i _
    fin_cases i
    · simp [v]
    · simp [v]
      ring

/-- The degree bound is needed: `X * (X - 1)`, of degree `2 = #univ`, vanishes at both nodes, but
it is not the combination of the interpolants of the zero values, which is `0`. -/
example : ¬∀ P : ℚ[X],
    (∀ i ∈ (univ : Finset (Fin 2)), P.eval (RingHom.id ℚ (v i)) =
      RingHom.id ℚ ((0 : Fin 2 → ℚ) i) + 1 * RingHom.id ℚ ((0 : Fin 2 → ℚ) i)) →
    P = (interpolate univ v 0).map (RingHom.id ℚ) +
      C 1 * (interpolate univ v 0).map (RingHom.id ℚ) := by
  intro h
  have := h (X * (X - 1)) (by intro i _; fin_cases i <;> simp [v])
  simp only [map_zero, Polynomial.map_zero, mul_zero, add_zero] at this
  exact mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1) this

/-- Injectivity of the nodes is needed: with both nodes at `0`, the polynomial `X` has degree
below `2` and takes the value `0` at every node, but it is not the combination of the
interpolants of the zero values. -/
example : ¬∀ P : ℚ[X], P.degree < #(univ : Finset (Fin 2)) →
    (∀ i ∈ (univ : Finset (Fin 2)), P.eval (RingHom.id ℚ ((fun _ ↦ 0 : Fin 2 → ℚ) i)) =
      RingHom.id ℚ ((0 : Fin 2 → ℚ) i) + 1 * RingHom.id ℚ ((0 : Fin 2 → ℚ) i)) →
    P = (interpolate univ (fun _ ↦ 0 : Fin 2 → ℚ) 0).map (RingHom.id ℚ) +
      C 1 * (interpolate univ (fun _ ↦ 0 : Fin 2 → ℚ) 0).map (RingHom.id ℚ) := by
  intro h
  have := h X (by rw [card_univ, Fintype.card_fin, degree_X]; decide) (by simp)
  simp only [map_zero, Polynomial.map_zero, mul_zero, add_zero] at this
  exact X_ne_zero this

section Frobenius

/-- The nodes `0, 1` over `ZMod 2`. -/
def w : Fin 2 → ZMod 2 := ![0, 1]

lemma w_injOn : Set.InjOn w (univ : Finset (Fin 2)) := by
  intro i _ j _ h
  fin_cases i <;> fin_cases j <;> simp_all [w]

/-- Over `ZMod 2`, `X ^ 2 + 1` has degree below `2 * 2`, is sparse at `0`, and takes the values
`1, 0` at the square roots `0, 1` of the nodes. It is recognized as `expand` of the interpolant of
those values. -/
example : (X ^ 2 + 1 : (ZMod 2)[X]) = expand (ZMod 2) (2 ^ 1)
    ((interpolate univ w ![1, 0]).map (RingHom.id _) +
      C 0 * (interpolate univ w 0).map (RingHom.id _)) := by
  apply eq_expand_map_interpolate_add_C_mul_of_eval_eq _ w_injOn _ _ _ 2 1 w
  · intro i _
    fin_cases i <;> simp [w]
  · rw [card_univ, Fintype.card_fin]
    compute_degree!
  · intro j hj
    rw [taylor_zero, coeff_add, coeff_X_pow, coeff_one]
    have h2 : j ≠ 2 := by rintro rfl; exact hj ⟨1, rfl⟩
    have h0 : j ≠ 0 := by rintro rfl; exact hj ⟨0, rfl⟩
    simp [h2, h0]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    intro i _
    fin_cases i <;> simp [w, h11]

/-- The sparsity hypothesis is needed: `X ^ 3 - X` over `ZMod 2` has degree below `2 * 2` and
vanishes at the square roots `0, 1` of both nodes, but it is not `expand` of the zero
interpolants. -/
example : ¬∀ P : (ZMod 2)[X], P.degree < ((2 ^ 1 * #(univ : Finset (Fin 2)) : ℕ) : WithBot ℕ) →
    (∀ i ∈ (univ : Finset (Fin 2)), P.eval (w i) =
      RingHom.id _ ((0 : Fin 2 → ZMod 2) i) + 0 * RingHom.id _ ((0 : Fin 2 → ZMod 2) i)) →
    P = expand (ZMod 2) (2 ^ 1) ((interpolate univ w 0).map (RingHom.id _) +
      C 0 * (interpolate univ w 0).map (RingHom.id _)) := by
  intro h
  have := h (X ^ 3 - X) (by rw [card_univ, Fintype.card_fin]; norm_num; compute_degree!)
    (by intro i _; fin_cases i <;> simp [w])
  simp only [map_zero, Polynomial.map_zero, mul_zero, add_zero] at this
  simpa using congrArg (coeff · 1) this

end Frobenius

end LagrangeLineTest
