/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.DivisorReconstruction
import ArkLib.Data.Polynomial.FractionFieldResultant
import ArkLib.Data.Polynomial.FrobeniusContraction
import ArkLib.Data.Polynomial.PointCollisionProbability
import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.SpecializationAvoidance
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

open Polynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### Divisor reconstruction -/

-- A repeated anchor still gives a degree-two nodal divisor.
example :
    (Lagrange.nodal Finset.univ ![(2 : ℚ), 2] * (1 : ℚ[X]) + 0).degree < 3 := by
  apply degree_nodal_mul_add_lt Finset.univ ![(2 : ℚ), 2] (k := 1)
  · simp
  · exact WithBot.bot_lt_coe 2

-- At an anchor, reconstruction takes the correction's value.
example :
    (Lagrange.nodal Finset.univ ![(1 : ℚ), 5] * X + C 3).eval 5 = 3 := by
  simpa using eval_nodal_mul_add_at_node (s := Finset.univ) (v := ![(1 : ℚ), 5])
    (Finset.mem_univ 1) X (C 3 : ℚ[X])

-- The quotient equation also applies over a ring with zero divisors.
example : ((X - C 0 : (ZMod 4)[X]) * C 2 + C 3).eval 2 = 3 :=
  eval_mul_add_of_eval_mul_eq_sub (by
    simp only [map_zero, sub_zero, eval_X, eval_C, sub_self]
    decide)

/-! ### Fraction-field derivative resultants -/

private noncomputable def artinSchreier : (ZMod 3)[X] := X ^ 3 - X

private theorem artinSchreier_derivative : artinSchreier.derivative = -1 := by
  have hthree : ((3 : ℕ) : ZMod 3) = 0 := CharP.cast_eq_zero _ 3
  simp only [artinSchreier, derivative_sub, derivative_pow, derivative_X]
  rw [hthree]
  simp

private theorem artinSchreier_separable : artinSchreier.Separable := by
  rw [separable_def, artinSchreier_derivative]
  exact ⟨0, -1, by simp⟩

-- In characteristic three, the derivative degree drops, but the padded resultant is nonzero.
example : resultant artinSchreier artinSchreier.derivative 3 2 ≠ 0 := by
  have h := resultant_derivative_ne_zero_of_separable_map_fractionField
    (K := ZMod 3) artinSchreier (by simpa using artinSchreier_separable)
  simpa [artinSchreier, natDegree_sub_eq_left_of_natDegree_lt] using h

/-! ### Frobenius contraction -/

-- In characteristic two, `X ^ 2` contracts to `X` in one step.
example : ∃ e : ℕ, ∃ G : (ZMod 2)[X],
    derivative G ≠ 0 ∧ expand (ZMod 2) (2 ^ e) G = X ^ 2 ∧
      G.natDegree * 2 ^ e = (X ^ 2 : (ZMod 2)[X]).natDegree ∧ 0 < G.natDegree := by
  refine ⟨1, X, by simp, ?_, by norm_num, by norm_num⟩
  rw [pow_one, expand_X]

-- A polynomial with nonzero derivative cannot be a first Frobenius expansion.
example : ¬ ∃ H : (ZMod 2)[X], expand (ZMod 2) 2 H = X :=
  not_exists_expand_of_derivative_ne_zero 2 (by simp)

/-! ### Point collisions -/

namespace PointCollisionTest

noncomputable section

/-- The tuples `X ^ 2 - 1` and `0` of one coordinate differ. -/
theorem sq_sub_one_ne_zero : ![(X ^ 2 - 1 : ℚ[X])] ≠ ![0] := by
  intro h
  have := congrArg (eval 0) (congrFun h 0)
  simp at this

-- The pair `X ^ 2 - 1` and `0` collides at `1` and `-1`, attaining the bound `2`.
example : ({fun _ ↦ 1, fun _ ↦ -1} : Finset (Unit → ℚ)).card = 2 ∧
    ({fun _ ↦ 1, fun _ ↦ -1} : Finset (Unit → ℚ)).card ≤ 2 ^ Fintype.card Unit := by
  constructor
  · rw [Finset.card_pair]
    intro h
    have := congrFun h ()
    norm_num at this
  · exact card_le_of_evalTuple_eq sq_sub_one_ne_zero
      (fun j ↦ by fin_cases j; simp only [Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_fin_one]; compute_degree)
      (fun j ↦ by simp) _ fun x hx ↦ by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> funext i j <;> fin_cases j <;> simp

/-- The two tuples `X` and `0` over `ZMod 5`. -/
def pairX0 : Finset (Fin 1 → (ZMod 5)[X]) := {![X], ![0]}

theorem card_pairX0 : pairX0.card = 2 := by
  refine Finset.card_pair fun h ↦ ?_
  have := congrArg (eval 1) (congrFun h 0)
  simp only [Fin.isValue, Matrix.cons_val_fin_one, eval_X, eval_zero] at this
  exact absurd this (by decide)

theorem natDegree_pairX0 : ∀ f ∈ pairX0, ∀ j, (f j).natDegree ≤ 1 := by
  intro f hf j
  simp only [pairX0, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl <;> fin_cases j <;> simp

-- A uniform point of `ZMod 5` separates `X` and `0` except with probability `1 / 5`.
open scoped ProbabilityTheory in
example : Pr{let ω ← $ᵗ (ZMod 5)}[¬ Set.InjOn (evalTuple fun _ : Unit ↦ ω)
    (↑pairX0 : Set (Fin 1 → (ZMod 5)[X]))] ≤ ENNReal.ofReal (1 / 5) := by
  have h := prob_not_injOn_evalTuple_le (Ω := ZMod 5) (pt := fun ω _ ↦ ω)
    (fun _ _ h ↦ congrFun h ()) pairX0 natDegree_pairX0
  rw [card_pairX0] at h
  simpa [ZMod.card] using h

end

end PointCollisionTest

/-! ### Resultant degree bounds -/

-- The weighted total-degree bound is sharp for `Res(Y - X, Y + 1) = X + 1`.
example : (resultant (X - C (X : ℚ[X])) (X + C 1) 1 1).natDegree ≤ 1 := by
  apply natDegree_resultant_le_of_coeff_add_le _ _ 1 1 1 1
  · intro i hi
    interval_cases i <;> simp only [coeff_sub, coeff_X, coeff_C] <;> simp
  · intro i hi
    interval_cases i <;> simp only [coeff_add, coeff_X, coeff_C] <;> simp

/-! ### Specialization avoidance -/

namespace SpecializationAvoidanceTest

/-- `(T ^ 2 - 1) * Y + 1` over `ZMod 5`. Its leading coefficient vanishes at `T = 1` and `T = 4`.
-/
noncomputable def linear5 : (ZMod 5)[X][X] := C (X ^ 2 - C 1) * X + C 1

theorem linear5_coeff_ne_zero : (X ^ 2 - C 1 : (ZMod 5)[X]) ≠ 0 :=
  (monic_X_pow_sub_C (1 : ZMod 5) two_ne_zero).ne_zero

theorem linear5_natDegree : linear5.natDegree = 1 :=
  natDegree_linear linear5_coeff_ne_zero

theorem linear5_leadingCoeff : linear5.leadingCoeff = X ^ 2 - C 1 :=
  leadingCoeff_linear linear5_coeff_ne_zero

theorem linear5_ne_zero : linear5 ≠ 0 := fun h ↦
  linear5_coeff_ne_zero (by rw [← linear5_leadingCoeff, h, leadingCoeff_zero])

-- Over `ZMod 5`, with `T := univ` and `forbidden := {0}`, the finite candidate form gives a
-- nonzero `t` that keeps the outer degree; hence `t ^ 2 ≠ 1`.
example : ∃ t : ZMod 5, t ≠ 0 ∧ t ^ 2 ≠ 1 := by
  obtain ⟨t, -, ht0, hne, hdegree⟩ :=
    exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card linear5_ne_zero
      (T := Finset.univ) (forbidden := {0}) (by
        rw [linear5_leadingCoeff, natDegree_X_pow_sub_C]
        decide)
  refine ⟨t, by simpa using ht0, fun ht ↦ leadingCoeff_ne_zero.mpr hne ?_⟩
  have hcoeff : linear5.coeff 1 = X ^ 2 - C 1 := by
    rw [← linear5_natDegree]
    exact linear5_leadingCoeff
  rw [leadingCoeff, hdegree, linear5_natDegree, coeff_map, hcoeff, coe_evalRingHom, eval_sub,
    eval_pow, eval_X, eval_C, ht, sub_self]

end SpecializationAvoidanceTest

private noncomputable def canary : ℚ[X][X] := C X * X + C 1

private theorem canary_ne_zero : canary ≠ 0 := by
  intro h
  have hzero := congrArg (fun p : ℚ[X][X] => p.eval 0) h
  simp [canary] at hzero

-- Avoiding `1` preserves the outer degree of `T * Y + 1` over `ℚ`.
example : ∃ t : ℚ, t ≠ 1 ∧ canary.map (evalRingHom t) ≠ 0 ∧
    (canary.map (evalRingHom t)).natDegree = canary.natDegree := by
  simpa [canary] using exists_map_evalRingHom_ne_zero_avoiding canary canary_ne_zero {1}
