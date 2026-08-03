/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.ToCompPoly.Multilinear.Basic

/-!
  # Path-dependent evaluation trees for computable multilinear polynomials

  This file defines the binary evaluation trees used by the corrected special-soundness argument
  for Hachi Lemma 10.  At every level, the two sibling labels are distinct, while labels below a
  node may depend on the path taken to that node.  Thus these are genuine nested trees, not
  Cartesian grids or coordinate-wise stars.

  The public definitions and final zero-test are stated for CompPoly's computable
  `CMlPolynomialEval` representation.  Mathlib's `MvPolynomial` is used only inside the algebraic
  proof, through `CMlPolynomialEval.eval_eq_MvPolynomial_MLE`.
-/

namespace CompPoly.CMlPolynomialEval

/-- A complete binary evaluation tree of depth `n` over `F`.

Each node stores its two scalar challenge labels and the corresponding subtrees.  Since every
child stores its own later labels, challenges at later levels may depend on the earlier path. -/
inductive BinaryEvaluationTree (F : Type*) : (n : ℕ) → Type _ where
  /-- The unique shape at depth zero. -/
  | leaf : BinaryEvaluationTree F 0
  /-- A binary challenge node followed by one subtree for each challenge. -/
  | node {n : ℕ} (challenges : Fin 2 → F)
      (children : Fin 2 → BinaryEvaluationTree F n) : BinaryEvaluationTree F (n + 1)

namespace BinaryEvaluationTree

variable {F : Type*} {n : ℕ}

/-- Every pair of sibling challenge labels in the tree is distinct. -/
def IsDistinct : {n : ℕ} → BinaryEvaluationTree F n → Prop
  | 0, .leaf => True
  | _ + 1, .node challenges children =>
      Function.Injective challenges ∧ ∀ j, IsDistinct (children j)

/-- An evaluation function vanishes at every leaf point of a binary evaluation tree.

At a node, the selected challenge is prepended to the point assembled by the child.  This
recursive formulation keeps the path dependence explicit and avoids replacing the tree by a
Cartesian product. -/
def Vanishes [Zero F] : {n : ℕ} → BinaryEvaluationTree F n → ((Fin n → F) → F) → Prop
  | 0, .leaf, evalAt => evalAt (fun i => i.elim0) = 0
  | _ + 1, .node challenges children, evalAt =>
      ∀ j, Vanishes (children j) (fun x => evalAt (Fin.cons (challenges j) x))

/-- A computable multilinear polynomial vanishes at every point represented by `tree`. -/
def PolynomialVanishes [CommRing F]
    (tree : BinaryEvaluationTree F n) (p : CMlPolynomialEval F n) : Prop :=
  tree.Vanishes fun x => CMlPolynomialEval.eval p (Vector.ofFn x)

section ZeroTest

variable [Field F]

/-- Mathlib-only algebraic core of the nested-tree zero test.

The polynomial has individual degree at most one.  At a node, fixing the first variable preserves
that bound for every remaining variable; the induction hypothesis therefore makes both restricted
polynomials zero.  The original polynomial, regarded as univariate in its first variable over the
ring of polynomials in the remaining variables, then has two distinct roots and degree at most
one, so it is zero. -/
private theorem mvPolynomial_eq_zero_of_vanishes
    (tree : BinaryEvaluationTree F n) (p : MvPolynomial (Fin n) F)
    (hDegree : ∀ i, p.degreeOf i ≤ 1) (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval x p) : p = 0 := by
  classical
  induction tree with
  | leaf =>
      rw [MvPolynomial.eq_C_of_isEmpty p] at hVanishes ⊢
      simpa [Vanishes] using hVanishes
  | @node n challenges children ih =>
      rcases hDistinct with ⟨hChallenges, hChildren⟩
      let q : Polynomial (MvPolynomial (Fin n) F) := MvPolynomial.finSuccEquiv F n p
      have hRestrictedZero : ∀ j, q.eval (MvPolynomial.C (challenges j)) = 0 := by
        intro j
        apply ih j
        · intro i
          exact (MvPolynomial.degreeOf_eval_C_finSuccEquiv p i (challenges j)).trans
            (hDegree i.succ)
        · exact hChildren j
        · simpa only [q, MvPolynomial.eval_comp_eval_C_finSuccEquiv] using hVanishes j
      have hChallengeNe : challenges 0 ≠ challenges 1 := by
        intro h
        have : (0 : Fin 2) = 1 := hChallenges h
        omega
      let c₀ : MvPolynomial (Fin n) F := MvPolynomial.C (challenges 0)
      let c₁ : MvPolynomial (Fin n) F := MvPolynomial.C (challenges 1)
      have hcNe : c₀ ≠ c₁ := by
        simpa [c₀, c₁] using hChallengeNe
      let roots : Finset (MvPolynomial (Fin n) F) := {c₀, c₁}
      have hRootsCard : roots.card = 2 := by
        simp [roots, hcNe]
      have hDegreeQLe : q.natDegree ≤ 1 := by
        simpa [q, MvPolynomial.natDegree_finSuccEquiv] using hDegree 0
      have hDegreeQ : q.natDegree < roots.card := by
        rw [hRootsCard]
        omega
      have hRoots : ∀ x ∈ roots, q.eval x = 0 := by
        intro x hx
        simp only [roots, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simpa [c₀] using hRestrictedZero 0
        · simpa [c₁] using hRestrictedZero 1
      have hq : q = 0 :=
        Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q roots hRoots hDegreeQ
      exact EmbeddingLike.map_eq_zero_iff.mp hq

/-- **Nested binary zero test for computable multilinear polynomials.**

If a `CMlPolynomialEval F n` evaluates to zero at every leaf of a complete depth-`n` binary tree
whose sibling labels are distinct at every node, then the computable polynomial is the zero
evaluation table.  Later labels may depend on the earlier path.

The statement uses only CompPoly's computable representation and evaluator.  The proof transports
the table to its Mathlib multilinear extension with `eval_eq_MvPolynomial_MLE`, applies the private
algebraic tree lemma above, and transports the resulting zero identity back to the table. -/
theorem eq_zero_of_polynomialVanishes (tree : BinaryEvaluationTree F n)
    (p : CMlPolynomialEval F n) (hDistinct : tree.IsDistinct)
    (hVanishes : tree.PolynomialVanishes p) : p = 0 := by
  let evals : (Fin n → Fin 2) → F := fun x => p.get (finFunctionFinEquiv x)
  have hp : Vector.ofFn (fun i => evals (finFunctionFinEquiv.symm i)) = p := by
    apply Vector.ext
    intro i hi
    simp only [evals, Vector.getElem_ofFn, Equiv.apply_symm_apply]
    rfl
  have heval (x : Fin n → F) :
      CMlPolynomialEval.eval p (Vector.ofFn x) =
        MvPolynomial.eval x (MvPolynomial.MLE evals) := by
    rw [← hp]
    exact CMlPolynomialEval.eval_eq_MvPolynomial_MLE evals x
  have hMvVanishes :
      tree.Vanishes fun x => MvPolynomial.eval x (MvPolynomial.MLE evals) := by
    rw [← funext heval]
    exact hVanishes
  have hMvZero : MvPolynomial.MLE evals = 0 :=
    mvPolynomial_eq_zero_of_vanishes tree (MvPolynomial.MLE evals)
      (fun i => MvPolynomial.MLE_degreeOf evals i) hDistinct hMvVanishes
  rw [MvPolynomial.MLE_eq_zero_iff] at hMvZero
  apply Vector.ext
  intro i hi
  have h := hMvZero (finFunctionFinEquiv.symm ⟨i, hi⟩)
  simp only [evals] at h
  have heq : finFunctionFinEquiv (finFunctionFinEquiv.symm ⟨i, hi⟩) = ⟨i, hi⟩ :=
    Equiv.apply_symm_apply finFunctionFinEquiv ⟨i, hi⟩
  rw [heq] at h
  rw [Vector.get_eq_getElem] at h
  simpa only [Vector.getElem_zero] using h

end ZeroTest

end BinaryEvaluationTree

end CompPoly.CMlPolynomialEval
