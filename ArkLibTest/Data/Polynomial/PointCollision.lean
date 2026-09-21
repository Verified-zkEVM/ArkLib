/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.PointCollision
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

/-!
# Point-collision clients

These clients evaluate a concrete polynomial tuple, show that the single-pair bound `d ^ |ι|` is
attained by `X ^ 2 - 1` and `0` over `ℚ`, and show that its three hypotheses are needed: over
`ZMod 8` the same pair collides at four points, equal tuples collide everywhere, and a constant
sampling map fails with probability `1`. They also compute the probability bound `1 / 5` for the
pair `X, 0` at a uniform point of `ZMod 5`, and select the unique tuple with given point values.
-/

namespace PointCollisionTest

open Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable section

-- The values of `(X, X ^ 2)` at the points `2, 3`.
example : evalTuple ![(2 : ℚ), 3] ![X, X ^ 2] = ![![2, 4], ![3, 9]] := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The tuples `X ^ 2 - 1` and `0` of one coordinate differ. -/
theorem sq_sub_one_ne_zero : ![(X ^ 2 - 1 : ℚ[X])] ≠ ![0] := by
  intro h
  have := congrArg (eval 0) (congrFun h 0)
  simp at this

-- The pair collides at the two single points `1` and `-1`: the bound `2 ^ 1` is attained.
example : ({fun _ ↦ 1, fun _ ↦ -1} : Finset (Unit → ℚ)).card ≤ 2 ^ Fintype.card Unit :=
  card_le_of_evalTuple_eq sq_sub_one_ne_zero
    (fun j ↦ by fin_cases j; simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one];
                compute_degree)
    (fun j ↦ by simp) _ fun x hx ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> funext i j <;> fin_cases j <;> simp

example : ({fun _ ↦ 1, fun _ ↦ -1} : Finset (Unit → ℚ)).card = 2 := by
  rw [Finset.card_pair]
  intro h
  have := congrFun h ()
  norm_num at this

-- The domain hypothesis is needed: over `ZMod 8`, `X ^ 2 - 1` vanishes at `1, 3, 5, 7`, which is
-- more than `2 ^ 1` single points.
example : ¬ ∀ T : Finset (Unit → ZMod 8),
    (∀ x ∈ T, evalTuple x ![(X ^ 2 - 1 : (ZMod 8)[X])] = evalTuple x ![0]) →
      T.card ≤ 2 ^ Fintype.card Unit := by
  intro h
  have := h {fun _ ↦ 1, fun _ ↦ 3, fun _ ↦ 5, fun _ ↦ 7} fun x hx ↦ by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> funext i j <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, evalTuple_apply, Matrix.cons_val_fin_one, eval_sub,
        eval_pow, eval_X, eval_one, eval_zero] <;> decide
  revert this
  decide

-- `f ≠ g` is needed: a tuple collides with itself at every point, while the bound for `d = 0`
-- is `0`.
example : ¬ ∀ T : Finset (Unit → ℚ),
    (∀ x ∈ T, evalTuple x ![(1 : ℚ[X])] = evalTuple x ![1]) → T.card ≤ 0 ^ Fintype.card Unit := by
  intro h
  have := h {fun _ ↦ 0} (by simp)
  simp at this

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

open scoped ProbabilityTheory in
-- A uniform point of `ZMod 5` separates `X` and `0` except with probability `1 / 5`.
example : Pr_{let ω ←$ᵖ (ZMod 5)}[¬ Set.InjOn (evalTuple fun _ : Unit ↦ ω)
    (↑pairX0 : Set (Fin 1 → (ZMod 5)[X]))] ≤ ENNReal.ofReal (1 / 5) := by
  have h := prob_not_injOn_evalTuple_le (Ω := ZMod 5) (pt := fun ω _ ↦ ω)
    (fun _ _ h ↦ congrFun h ()) pairX0 natDegree_pairX0
  rw [card_pairX0] at h
  simpa [ZMod.card] using h

open scoped ProbabilityTheory in
-- Injectivity of the sampling map is needed: the constant point `0` never separates `X` and `0`,
-- so the failure probability is `1`, above the bound `1 / 2` for `|Ω| = 2`.
example : ¬ Pr_{let _ω ←$ᵖ Bool}[¬ Set.InjOn (evalTuple fun _ : Unit ↦ (0 : ZMod 5))
    (↑pairX0 : Set (Fin 1 → (ZMod 5)[X]))] ≤
      ENNReal.ofReal (((Nat.choose 2 2 * 1 ^ 1 : ℕ) : ℝ) / 2) := by
  classical
  have hevent : ¬ Set.InjOn (evalTuple fun _ : Unit ↦ (0 : ZMod 5))
      (↑pairX0 : Set (Fin 1 → (ZMod 5)[X])) := by
    intro h
    have := h (x₁ := ![X]) (x₂ := ![0]) (by simp [pairX0]) (by simp [pairX0])
      (by funext i j; fin_cases j; simp)
    have := congrArg (eval 1) (congrFun this 0)
    simp only [Fin.isValue, Matrix.cons_val_fin_one, eval_X, eval_zero] at this
    exact absurd this (by decide)
  rw [Probability.prob_uniform_eq_ofReal]
  simp only [hevent, not_false_eq_true, Finset.filter_true,
    Finset.card_univ, Fintype.card_bool]
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

-- Separating points select the unique tuple with the claimed values.
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
