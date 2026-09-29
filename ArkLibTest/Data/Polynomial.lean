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
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

/-! # Polynomial acceptance tests -/

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

-- Multiplying two linear polynomials and adding a constant stays below degree three.
example : ((X : ℚ[X]) * X + C 1).degree < 3 := by
  apply degree_mul_add_lt (D := X) (q := X) (I := C 1) (d := 1) (k := 2)
  · simp
  · simp
  · simp

-- A root of the divisor preserves the correction value.
example : ((X - C 1 : ℚ[X]) * X + C 3).eval 1 = 3 := by
  rw [eval_mul_add_of_eval_eq_zero (D := X - C 1) (q := X) (I := C 3)
    (x := 1) (by simp)]
  simp

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

private theorem irreducible_Y_sq_sub_t : Irreducible (X ^ 2 - C X : ℚ[X][X]) := by
  have hmonic : (X ^ 2 - C X : ℚ[X][X]).Monic := by monicity!
  have hdeg : (X ^ 2 - C X : ℚ[X][X]).natDegree = 2 := by compute_degree!
  rw [Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr ↦ ?_
  rw [mem_roots hmonic.ne_zero, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  have h := congrArg natDegree hr
  rw [natDegree_pow, natDegree_X] at h
  omega

-- The irreducible polynomial `Y ^ 2 - t` over `ℚ[t]` has nonzero padded derivative resultant.
example : resultant (X ^ 2 - C X : ℚ[X][X])
    (X ^ 2 - C X : ℚ[X][X]).derivative 2 1 ≠ 0 := by
  have h := resultant_derivative_ne_zero_of_irreducible _ irreducible_Y_sq_sub_t
    (by simp [derivative_sub])
  have hdeg : (X ^ 2 - C X : ℚ[X][X]).natDegree = 2 := by compute_degree!
  rwa [hdeg] at h

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

-- The irreducible polynomial `2X + 1` over `ℤ` contracts to an irreducible separable polynomial
-- over its fraction field `ℚ` in characteristic zero.
example : ∃ e : ℕ, ∃ G : ℤ[X],
    derivative G ≠ 0 ∧ expand ℤ (0 ^ e) G = C 2 * X + 1 ∧
      G.natDegree * 0 ^ e = (C 2 * X + 1 : ℤ[X]).natDegree ∧
      0 < G.natDegree ∧ Irreducible G ∧
      Irreducible (G.map (algebraMap ℤ ℚ)) ∧ (G.map (algebraMap ℤ ℚ)).Separable := by
  have hirr : Irreducible (C 2 * X + 1 : ℤ[X]) := by
    simpa only [C_1] using irreducible_C_mul_X_add_C (two_ne_zero : (2 : ℤ) ≠ 0)
      isRelPrime_one_right
  have hdeg : 0 < (C 2 * X + 1 : ℤ[X]).natDegree := by
    rw [← C_1, natDegree_linear two_ne_zero]
    exact Nat.one_pos
  exact exists_frobeniusContraction_fractionRing (K := ℚ) 0 hdeg hirr

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

-- At the common root `0`, the two degree-one tuples fail to separate.
example :
    ({fun _ : Unit ↦ (0 : ℚ)} : Finset (Unit → ℚ)).card ≤
      ({![(X : ℚ[X])], ![0]} : Finset (Fin 1 → ℚ[X])).card.choose 2 *
        1 ^ Fintype.card (Fin 1) := by
  let S : Finset (Fin 1 → ℚ[X]) := {![X], ![0]}
  let T : Finset (Unit → ℚ) := {fun _ ↦ (0 : ℚ)}
  have hdegree : ∀ f ∈ S, ∀ j, (f j).natDegree ≤ 1 := by
    intro f hf j
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl <;> fin_cases j <;> simp
  have hfail : ∀ x ∈ T, ¬ Set.InjOn (evalTuple x) (S : Set (Fin 1 → ℚ[X])) := by
    intro x hx
    simp only [T, Finset.mem_singleton] at hx
    subst x
    intro hinj
    have hvalues : evalTuple (fun _ : Unit ↦ (0 : ℚ)) ![X] =
        evalTuple (fun _ : Unit ↦ (0 : ℚ)) ![0] := by
      funext i j
      simp
    have hne : (![X] : Fin 1 → ℚ[X]) ≠ ![0] := by
      intro h
      have := congrArg (eval 1) (congrFun h 0)
      simp at this
    exact hne (hinj (x₁ := ![X]) (x₂ := ![0]) (by simp [S]) (by simp [S]) hvalues)
  exact card_le_of_not_injOn_evalTuple S hdegree T hfail

-- A uniform point of `ZMod 5` separates `X` and `0` except with probability `1 / 5`.
open scoped ProbabilityTheory in
example : Pr{let ω ← $ᵗ (ZMod 5)}[¬ Set.InjOn (evalTuple fun _ : Unit ↦ ω)
    (↑pairX0 : Set (Fin 1 → (ZMod 5)[X]))] ≤ ENNReal.ofReal (1 / 5) := by
  have h := prob_not_injOn_evalTuple_le (Ω := ZMod 5) (pt := fun ω _ ↦ ω)
    (fun _ _ h ↦ congrFun h ()) pairX0 natDegree_pairX0
  rw [card_pairX0] at h
  simpa [ZMod.card] using h

-- The singleton family containing `X` has one possible exceptional root.
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧
    ∀ z ∉ exceptional, ∀ _i : Fin 1,
      (X : ℚ[X]).eval z = 0 ↔ (X : ℚ[X]) = 0 := by
  exact exists_card_le_forall_eval_eq_zero_iff
    (fun _ : Fin 1 ↦ (X : ℚ[X])) (d := 1) Finset.univ
    (by intro i hi; simp) (by intro i hi; exact (hi (Finset.mem_univ i)).elim)

-- Separating points select the unique tuple `X` with its value at `1`.
example : ∃ o : Option (Fin 1 → (ZMod 5)[X]),
    ∀ f, o = some f ↔ f ∈ (↑pairX0 : Set (Fin 1 → (ZMod 5)[X])) ∧
      evalTuple (fun _ : Unit ↦ (1 : ZMod 5)) f =
        evalTuple (fun _ : Unit ↦ (1 : ZMod 5)) ![X] := by
  refine exists_option_eq_some_iff_of_injOn_evalTuple ?_ _
  intro f hf g hg h
  simp only [pairX0, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hf hg
  have h1 := congrFun (congrFun h ()) 0
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;>
    first
    | rfl
    | (simp only [evalTuple_apply, Fin.isValue, Matrix.cons_val_fin_one, eval_X,
          eval_zero] at h1
       exact absurd h1 (by decide))

end

end PointCollisionTest

/-! ### Resultant degree bounds -/

-- `Res_Y(Y - X, Y ^ 2 + X ^ 3) = X ^ 2 + X ^ 3`, attaining the weighted degree bound.
private theorem resultant_line_cubic :
    resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2 =
      (X : ℚ[X]) ^ 2 + X ^ 3 := by
  rw [resultant_X_sub_C_left _ _ _ (by compute_degree!)]
  simp

example :
    (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree = 3 ∧
      (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree + 1 * 2 ≤
        2 * 1 + 1 * 3 ∧
      (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree ≤
        2 * 1 + 1 * 3 - 1 * 2 ∧
      (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree ≤ 1 * 3 := by
  have hP : ∀ i ≤ 1, i + ((X - C (X : ℚ[X])).coeff i).natDegree ≤ 1 := by
    intro i hi
    interval_cases i <;> simp only [coeff_sub, coeff_X, coeff_C] <;> simp
  have hQ : ∀ i ≤ 2, i + ((X ^ 2 + C (X ^ 3 : ℚ[X])).coeff i).natDegree ≤ 3 := by
    intro i hi
    interval_cases i <;> simp only [coeff_add, coeff_X_pow, coeff_C] <;> simp
  refine ⟨by rw [resultant_line_cubic]; compute_degree!, ?_, ?_, ?_⟩
  · exact natDegree_resultant_add_mul_le_of_coeff_add_le _ _ 1 2 1 3 hP hQ
  · exact natDegree_resultant_le_of_coeff_add_le _ _ 1 2 1 3 hP hQ
  · exact natDegree_resultant_le_mul_of_coeff_add_le _ _ 1 2 1 3 hP hQ

-- Differentiating the outer variable preserves the coefficient-variable degree of `X^3 * Y^2`.
example :
    Bivariate.degreeX ((C ((X : ℚ[X]) ^ 3) * X ^ 2 : ℚ[X][X]).derivative) ≤
      Bivariate.degreeX (C ((X : ℚ[X]) ^ 3) * X ^ 2 : ℚ[X][X]) :=
  Bivariate.degreeX_derivative_le _

private noncomputable def squareEquation : ℚ[X][X] := X ^ 2 - C ((X : ℚ[X]) ^ 2)

private theorem resultant_squareEquation_derivative :
    resultant squareEquation squareEquation.derivative 2 1 = -4 * X ^ 2 := by
  have hder : squareEquation.derivative = C 2 * (X - C 0) := by
    simp only [squareEquation, derivative_sub, derivative_X_pow, derivative_C, C_0, sub_zero]
    simp
  rw [← resultant_comm_sub_one, hder, resultant_C_mul_left,
    show (2 : ℕ) - 1 = 1 from rfl,
    resultant_X_sub_C_left _ _ _ (by rw [squareEquation]; compute_degree!)]
  simp [squareEquation]
  ring

-- The total-degree padded-derivative bound is attained by `Y²-X²` over `ℚ`.
example :
    (resultant squareEquation squareEquation.derivative 2 1).natDegree = 2 ∧
      (resultant squareEquation squareEquation.derivative 2 1).natDegree + 2 ^ 2 ≤
        (2 * 2 - 1) * 2 ∧
      (resultant squareEquation squareEquation.derivative 2 1).natDegree ≤
        (2 * 2 - 1) * 2 - 2 ^ 2 := by
  have hcoeff : ∀ i ≤ 2, i + (squareEquation.coeff i).natDegree ≤ 2 := by
    intro i hi
    interval_cases i <;> simp only [squareEquation, coeff_sub, coeff_X_pow, coeff_C] <;> simp
  refine ⟨by rw [resultant_squareEquation_derivative]; compute_degree!, ?_, ?_⟩
  · exact natDegree_resultant_derivative_padded_add_sq_le squareEquation 2 2 hcoeff
  · exact natDegree_resultant_derivative_padded_le_of_coeff_add_le squareEquation 2 2 hcoeff

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
