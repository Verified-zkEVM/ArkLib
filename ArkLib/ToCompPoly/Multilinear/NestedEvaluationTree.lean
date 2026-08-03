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

@[simp]
theorem isDistinct_cast {m : ℕ} (h : n = m) (tree : BinaryEvaluationTree F n) :
    (h ▸ tree).IsDistinct ↔ tree.IsDistinct := by
  subst h
  rfl

/-- An evaluation function vanishes at every leaf point of a binary evaluation tree.

At a node, the selected challenge is prepended to the point assembled by the child.  This
recursive formulation keeps the path dependence explicit and avoids replacing the tree by a
Cartesian product. -/
def Vanishes [Zero F] : {n : ℕ} → BinaryEvaluationTree F n → ((Fin n → F) → F) → Prop
  | 0, .leaf, evalAt => evalAt (fun i => i.elim0) = 0
  | _ + 1, .node challenges children, evalAt =>
      ∀ j, Vanishes (children j) (fun x => evalAt (Fin.cons (challenges j) x))

@[simp]
theorem vanishes_cast [Zero F] {m : ℕ} (h : n = m) (tree : BinaryEvaluationTree F n)
    (evalAt : (Fin m → F) → F) :
    (h ▸ tree).Vanishes evalAt ↔
      tree.Vanishes (fun x => evalAt fun i => x (Fin.cast h.symm i)) := by
  subst h
  rfl

@[simp]
theorem vanishes_mpr [Zero F] {m : ℕ} (h : n = m) (tree : BinaryEvaluationTree F m)
    (evalAt : (Fin n → F) → F) :
    (Eq.mpr (congrArg (BinaryEvaluationTree F) h) tree).Vanishes evalAt ↔
      tree.Vanishes (fun x => evalAt fun i => x (Fin.cast h i)) := by
  subst h
  rfl

@[simp]
theorem vanishes_cast_rev [Zero F] {m : ℕ} (h : n = m) (tree : BinaryEvaluationTree F m)
    (evalAt : (Fin n → F) → F) :
    (h.symm ▸ tree).Vanishes evalAt ↔
      tree.Vanishes (fun x => evalAt fun i => x (Fin.cast h i)) := by
  subst h
  rfl

/-- A computable multilinear polynomial vanishes at every point represented by `tree`. -/
def PolynomialVanishes [CommRing F]
    (tree : BinaryEvaluationTree F n) (p : CMlPolynomialEval F n) : Prop :=
  tree.Vanishes fun x => CMlPolynomialEval.eval p (Vector.ofFn x)

/-! ## Prefix and suffix projections -/

/-- Retain the first `m` levels of a binary evaluation tree. -/
def take : {n : ℕ} → (tree : BinaryEvaluationTree F n) →
    (m : ℕ) → m ≤ n → BinaryEvaluationTree F m
  | _, _, 0, _ => .leaf
  | _ + 1, .node challenges children, m + 1, h =>
      .node challenges fun j => take (children j) m (by omega)

/-- Follow child `0` through the first `m` levels and retain the remaining suffix tree. -/
def dropLeft : {n : ℕ} → (tree : BinaryEvaluationTree F n) →
    (m : ℕ) → m ≤ n → BinaryEvaluationTree F (n - m)
  | _, tree, 0, _ => tree
  | n + 1, .node _ children, m + 1, h =>
      (Nat.succ_sub_succ_eq_sub n m).symm ▸ dropLeft (children 0) m (by omega)

/-- Restrict a point to its first `m` coordinates. -/
def pointPrefix {n : ℕ} (m : ℕ) (h : m ≤ n) (x : Fin n → F) : Fin m → F :=
  fun i => x (Fin.castLE h i)

/-- Restrict a point to the `n - m` coordinates following its first `m` coordinates. -/
def pointSuffix {n : ℕ} (m : ℕ) (h : m ≤ n) (x : Fin n → F) : Fin (n - m) → F :=
  fun i => x ⟨m + i, by omega⟩

/-- Prefix projection preserves sibling distinctness. -/
theorem take_isDistinct (tree : BinaryEvaluationTree F n) (m : ℕ) (hm : m ≤ n)
    (h : tree.IsDistinct) : (tree.take m hm).IsDistinct := by
  induction tree generalizing m with
  | leaf =>
      have : m = 0 := by omega
      subst m
      trivial
  | node challenges children ih =>
      cases m with
      | zero => trivial
      | succ m => exact ⟨h.1, fun j => ih j m (by omega) (h.2 j)⟩

/-- Following a fixed prefix preserves sibling distinctness in the retained suffix. -/
theorem dropLeft_isDistinct (tree : BinaryEvaluationTree F n) (m : ℕ) (hm : m ≤ n)
    (h : tree.IsDistinct) : (tree.dropLeft m hm).IsDistinct := by
  induction tree generalizing m with
  | leaf =>
      have : m = 0 := by omega
      subst m
      exact h
  | node challenges children ih =>
      cases m with
      | zero => exact h
      | succ m =>
          simpa only [dropLeft, isDistinct_cast] using ih 0 m (by omega) (h.2 0)

/-- A constant function that vanishes on a nonempty complete tree is zero. -/
theorem eq_zero_of_constant_vanishes [Zero F] (tree : BinaryEvaluationTree F n) (c : F)
    (h : tree.Vanishes fun _ => c) : c = 0 := by
  induction tree with
  | leaf => exact h
  | node challenges children ih =>
      exact ih 0 (h 0)

/-- Vanishing on a full tree implies vanishing on its prefix projection when the evaluated
function depends only on the retained prefix. -/
theorem take_vanishes [Zero F] (tree : BinaryEvaluationTree F n) (m : ℕ) (hm : m ≤ n)
    (evalAt : (Fin m → F) → F)
    (h : tree.Vanishes fun x => evalAt (pointPrefix m hm x)) :
    (tree.take m hm).Vanishes evalAt := by
  induction tree generalizing m with
  | leaf =>
      have : m = 0 := by omega
      subst m
      exact h
  | @node n challenges children ih =>
      cases m with
      | zero =>
          have hc : (BinaryEvaluationTree.node challenges children).Vanishes
              (fun _ => evalAt fun i => i.elim0) := by
            convert h using 1
            funext x
            congr 1
            exact Subsingleton.elim _ _
          exact (BinaryEvaluationTree.node challenges children).eq_zero_of_constant_vanishes
            (evalAt fun i => i.elim0) hc
      | succ m =>
          intro j
          apply ih j m (by omega)
          convert h j using 1
          funext x
          congr 1
          funext i
          exact Fin.cases rfl (fun i => rfl) i

/-- Vanishing on a full tree implies vanishing on the suffix subtree reached by repeatedly taking
child `0`, when the evaluated function depends only on that suffix. -/
theorem dropLeft_vanishes [Zero F] (tree : BinaryEvaluationTree F n) (m : ℕ) (hm : m ≤ n)
    (evalAt : (Fin (n - m) → F) → F)
    (h : tree.Vanishes fun x => evalAt (pointSuffix m hm x)) :
    (tree.dropLeft m hm).Vanishes evalAt := by
  induction tree generalizing m with
  | leaf =>
      have : m = 0 := by omega
      subst m
      simp only [dropLeft]
      convert h using 1
      funext x
      congr 1
      funext i
      exact i.elim0
  | @node n challenges children ih =>
      cases m with
      | zero =>
          simp only [Nat.sub_zero, dropLeft] at evalAt h ⊢
          convert h using 1
          funext x
          congr 1
          funext i
          simp only [pointSuffix]
          congr 1
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
      | succ m =>
          simp only [dropLeft, vanishes_cast]
          apply ih 0 m (by omega)
          convert h 0 using 1
          funext x
          congr 1
          funext i
          simp only [pointSuffix]
          rw [show (⟨m + 1 + i, by omega⟩ : Fin (n + 1)) =
            Fin.succ ⟨m + i, by omega⟩ by apply Fin.ext; simp only [Fin.val_succ]; omega]
          rfl

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
