/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.Interpolation
import ArkLib.ToCompPoly.Multilinear.NestedEvaluationTree
import Mathlib.Algebra.Field.ZMod

/-!
# Nested evaluation trees with per-level arities: concrete tests

Over `ZMod 5`, a tree of depth two with three labels at the first level and two at the second, the
second level's labels depending on the first label. The tests apply the zero test, show that its
strict degree bound and the positivity of the arities are load-bearing, count the leaves, and
derive the Cartesian-grid zero test as a corollary.
-/

open MvPolynomial NestedEvaluationTree

namespace NestedEvaluationTreeTest

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Three labels at the first level, two at the second. -/
def k : Fin 2 → ℕ := ![3, 2]

/-- The labels `0, 1, 2` at the first level; below the label `a`, the labels `a` and `a + 1`. -/
def tree : NestedEvaluationTree (ZMod 5) 2 k :=
  .node ![0, 1, 2] fun a => .node ![(a : ZMod 5), (a : ZMod 5) + 1] fun _ => .leaf

theorem injective_pair {x y : ZMod 5} (h : x ≠ y) : Function.Injective ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (by simpa using hij) h
  · exact absurd (by simpa using hij.symm) h
  · rfl

theorem injective_triple : Function.Injective (![0, 1, 2] : Fin 3 → ZMod 5) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> (revert h; decide)

theorem tree_isDistinct : tree.IsDistinct := by
  refine ⟨injective_triple, fun a => ⟨injective_pair fun h => ?_, fun _ => trivial⟩⟩
  have := congrArg (fun z => z - ((a : ℕ) : ZMod 5)) h
  simp at this

/-- A tree has `∏ i, k i` leaves; here `3 * 2 = 6`. -/
example : tree.numLeaves = 6 := by
  rw [numLeaves_eq_prod, Fin.prod_univ_two]
  rfl

#eval tree.numLeaves

/-- The zero test at arities `(3, 2)`: individual degree below `3` in the first variable and below
`2` in the second. -/
example (p : MvPolynomial (Fin 2) (ZMod 5)) (h0 : p.degreeOf 0 < 3) (h1 : p.degreeOf 1 < 2)
    (hv : tree.Vanishes fun x => eval x p) : p = 0 :=
  eq_zero_of_vanishes_comp (k := k) (fun i => by fin_cases i <;> decide) tree p id
    (fun i => (Nat.zero_add _).symm) (fun i => by fin_cases i <;> assumption)
    tree_isDistinct hv

/-- The strict degree bound is load-bearing: `T * (T - 1)` has individual degree `2 = k 0` and
vanishes at the two labels `0` and `1` of a binary level, but it is not zero. -/
example :
    let t : NestedEvaluationTree (ZMod 5) 1 ![2] := .node ![0, 1] fun _ => .leaf
    let p : MvPolynomial (Fin 1) (ZMod 5) := X 0 * (X 0 + C 4)
    p.degreeOf 0 ≤ 2 ∧ t.Vanishes (fun x => eval x p) ∧ p ≠ 0 := by
  intro t p
  refine ⟨?_, ?_, ?_⟩
  · calc p.degreeOf 0 ≤ (X 0 : MvPolynomial (Fin 1) (ZMod 5)).degreeOf 0 +
          (X 0 + C 4 : MvPolynomial (Fin 1) (ZMod 5)).degreeOf 0 := degreeOf_mul_le _ _ _
      _ ≤ 1 + (max 1 0) := by
          refine add_le_add (by rw [degreeOf_X]; simp) ?_
          refine (degreeOf_add_le _ _ _).trans ?_
          rw [degreeOf_X, degreeOf_C]
          simp
      _ = 2 := by norm_num
  · intro j
    change eval (Fin.cons (![0, 1] j) (fun i : Fin 0 => i.elim0) : Fin 1 → ZMod 5) p = 0
    simp only [p, map_mul, map_add, eval_X, eval_C, Fin.cons_zero]
    fin_cases j <;> decide
  · intro h
    have := congrArg (eval fun _ => (2 : ZMod 5)) h
    revert this
    simp only [p, map_mul, map_add, eval_X, eval_C, map_zero]
    decide

/-- Every level needs at least one label, including the levels outside the window: a tree whose
only level has no labels has no leaves, so every evaluation function vanishes on it, and the
constant polynomial `1` in no variable is not zero. -/
example :
    let t : NestedEvaluationTree (ZMod 5) 1 ![0] := .node ![] fun _ => .leaf
    let p : MvPolynomial (Fin 0) (ZMod 5) := 1
    t.IsDistinct ∧ t.Vanishes (fun x => eval (x ∘ fun i : Fin 0 => i.elim0) p) ∧ p ≠ 0 := by
  intro t p
  exact ⟨⟨fun a => a.elim0, fun j => j.elim0⟩, fun j => j.elim0, one_ne_zero⟩

/-- The product `{0, 1, 2} × {0, 1}` of the two label sets. -/
def S : Fin 2 → Finset (ZMod 5) := ![{0, 1, 2}, {0, 1}]

theorem card_S : ∀ i, (S i).card = k i := by decide

/-- The Cartesian-grid zero test on the product `{0, 1, 2} × {0, 1}`, which is the tree above with
path-independent labels. -/
example (p : MvPolynomial (Fin 2) (ZMod 5)) (h0 : p.degreeOf 0 < 3) (h1 : p.degreeOf 1 < 2)
    (hv : ∀ x ∈ Fintype.piFinset S, eval x p = 0) : p = 0 :=
  eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin S
    (fun i => by
      rw [card_S i]
      fin_cases i
      · exact h0
      · exact h1) hv

/-- The grid tree of a pair of label lists has one leaf per choice of one label per level. -/
example : (grid (k := k) fun i j => ((j : ℕ) : ZMod 5) + i).numLeaves = 6 := by
  rw [numLeaves_eq_prod, Fin.prod_univ_two]
  rfl

/-- A computable multilinear polynomial that vanishes on a tree with arities `(2, 3)`, read through
the first level, is zero: the window reads the binary level and the tree also has a ternary level
below it. -/
example {t : NestedEvaluationTree (ZMod 5) 2 ![2, 3]} (p : CompPoly.CMlPolynomialEval (ZMod 5) 1)
    (hd : t.IsDistinct)
    (hv : CompPoly.CMlPolynomialEval.PolynomialVanishes t p (Fin.castAdd 1)) : p = 0 :=
  CompPoly.CMlPolynomialEval.eq_zero_of_polynomialVanishes_castAdd (s := 1)
    (fun i => by fin_cases i <;> decide) t p
    (fun i => by obtain rfl : i = 0 := Subsingleton.elim _ _; exact le_rfl) hd hv

end NestedEvaluationTreeTest

/--
info: 'NestedEvaluationTree.eq_zero_of_vanishes_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NestedEvaluationTree.eq_zero_of_vanishes_comp

/--
info: 'NestedEvaluationTree.numLeaves_eq_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NestedEvaluationTree.numLeaves_eq_prod

/--
info: 'NestedEvaluationTree.vanishes_grid' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NestedEvaluationTree.vanishes_grid

/--
info: 'MvPolynomial.eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin

/--
info: 'CompPoly.CMlPolynomialEval.eq_zero_of_polynomialVanishes_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.CMlPolynomialEval.eq_zero_of_polynomialVanishes_comp
