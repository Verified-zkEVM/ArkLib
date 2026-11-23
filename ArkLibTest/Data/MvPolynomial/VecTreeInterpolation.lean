/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.VecTreeInterpolation
import Mathlib.Algebra.Field.ZMod

/-!
# Interpolation on challenge trees: concrete tests

Over `ZMod 5`, a challenge tree with three branches in the first round and two in the second. The
challenge of the second round depends on the branch of the first. The tests check that the tree is
structured, apply the interpolation, and show that its strict degree bound is load-bearing.
-/

open MvPolynomial Rewinding

namespace VecTreeInterpolationTest

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem natCast_inj {a b : ℕ} (ha : a < 5) (hb : b < 5) (h : (a : ZMod 5) = b) : a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b 5).mp h
  omega

/-- Three branches in the first round, two in the second. -/
def k : Fin 2 → ℕ := ![3, 2]

/-- The first-round challenge is the branch; the second-round challenge is the branch plus the
branch of the first round. -/
def tree : VecTree (fun _ : Fin 2 => ZMod 5) k where
  leaf p r := ((p r : ℕ) : ZMod 5) + if r = 1 then ((p 0 : ℕ) : ZMod 5) else 0
  causal p p' r h := by
    have h0 : p 0 = p' 0 := h 0 (Fin.zero_le r)
    fin_cases r
    · simp [h0]
    · have h1 : p 1 = p' 1 := h 1 le_rfl
      simp [h0, h1]

theorem k_pos : ∀ i, 0 < k i := fun i => by fin_cases i <;> decide

theorem lt_five (r : Fin 2) (a : Fin (k r)) : (a : ℕ) < 5 :=
  lt_of_lt_of_le a.2 (by fin_cases r <;> decide)

theorem tree_isStructured : tree.IsStructured fun _ ch => Function.Injective ch := by
  intro p r a b hab
  refine Fin.ext (natCast_inj (lt_five _ a) (lt_five _ b) ?_)
  fin_cases r <;> simpa [VecTree.siblings, tree] using hab

/-- The interpolation: individual degree below `3` in the first variable and below `2` in the
second, vanishing at the six leaves. -/
example (p : MvPolynomial (Fin 2) (ZMod 5)) (h0 : p.degreeOf 0 < 3) (h1 : p.degreeOf 1 < 2)
    (hv : ∀ path, eval (tree.leaf path) p = 0) : p = 0 :=
  VecTree.eq_zero_of_vanishes (k := k) k_pos tree tree_isStructured p
    (fun i => by fin_cases i <;> assumption) hv

/-- The nested tree of the challenge tree has `3 * 2 = 6` leaves. -/
example : (VecTree.toNested k_pos tree).numLeaves = 6 := by
  rw [NestedEvaluationTree.numLeaves_eq_prod, Fin.prod_univ_two]
  rfl

/-- The labels of the first level of a nested tree. -/
def firstLabels {n : ℕ} {k : Fin (n + 1) → ℕ} : NestedEvaluationTree (ZMod 5) (n + 1) k →
    List (ZMod 5)
  | .node challenges _ => List.ofFn challenges

/-- The labels of the second level, one list below each branch of the first level. -/
def secondLabels {n : ℕ} {k : Fin (n + 2) → ℕ} : NestedEvaluationTree (ZMod 5) (n + 2) k →
    List (List (ZMod 5))
  | .node _ children => List.ofFn fun j => firstLabels (children j)

/-! Runtime evidence: `toNested` runs. The first level carries the three first-round challenges,
and below branch `j` the second level carries `j` and `j + 1`. -/

/-- info: 6 -/
#guard_msgs in
#eval (VecTree.toNested k_pos tree).numLeaves

/-- info: [0, 1, 2] -/
#guard_msgs in
#eval firstLabels (VecTree.toNested k_pos tree)

/-- info: [[0, 1], [1, 2], [2, 3]] -/
#guard_msgs in
#eval secondLabels (VecTree.toNested k_pos tree)

/-- The strict degree bound is load-bearing: `T * (T - 1)` has individual degree `2 = k 0`, vanishes
at the two leaves of a binary round and is not zero. -/
example :
    let t : VecTree (fun _ : Fin 1 => ZMod 5) ![2] :=
      { leaf := fun p _ => ((p 0 : ℕ) : ZMod 5)
        causal := fun p p' _ h => by simp [h 0 (Fin.zero_le _)] }
    let p : MvPolynomial (Fin 1) (ZMod 5) := X 0 * (X 0 + C 4)
    t.IsStructured (fun _ ch => Function.Injective ch) ∧ p.degreeOf 0 ≤ 2 ∧
      (∀ path, eval (t.leaf path) p = 0) ∧ p ≠ 0 := by
  intro t p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q r a b hab
    obtain rfl : r = 0 := Subsingleton.elim _ _
    have ha : (a : ℕ) < 5 := by have := a.2; simp at this; omega
    have hb : (b : ℕ) < 5 := by have := b.2; simp at this; omega
    exact Fin.ext (natCast_inj ha hb (by simpa [VecTree.siblings, t] using hab))
  · calc p.degreeOf 0 ≤ (X 0 : MvPolynomial (Fin 1) (ZMod 5)).degreeOf 0 +
          (X 0 + C 4 : MvPolynomial (Fin 1) (ZMod 5)).degreeOf 0 := degreeOf_mul_le _ _ _
      _ ≤ 1 + (max 1 0) := by
          refine add_le_add (by rw [degreeOf_X]; simp) ?_
          refine (degreeOf_add_le _ _ _).trans ?_
          rw [degreeOf_X, degreeOf_C]
          simp
      _ = 2 := by norm_num
  · intro path
    have : ((path 0 : ℕ) : ZMod 5) = 0 ∨ ((path 0 : ℕ) : ZMod 5) = 1 := by
      have h := (path 0).2
      simp only [Matrix.cons_val_fin_one] at h
      interval_cases hx : (path 0 : ℕ) <;> simp
    rcases this with h | h
    · simp only [p, t, map_mul, map_add, eval_X, eval_C, h]
      decide
    · simp only [p, t, map_mul, map_add, eval_X, eval_C, h]
      decide
  · intro h
    have := congrArg (eval fun _ => (2 : ZMod 5)) h
    revert this
    simp only [p, map_mul, map_add, eval_X, eval_C, map_zero]
    decide

end VecTreeInterpolationTest

/--
info: 'Rewinding.VecTree.eq_zero_of_vanishes' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Rewinding.VecTree.eq_zero_of_vanishes

/--
info: 'Rewinding.VecTree.vanishes_toNested' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Rewinding.VecTree.vanishes_toNested

/--
info: 'Rewinding.VecTree.isDistinct_toNested' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Rewinding.VecTree.isDistinct_toNested
