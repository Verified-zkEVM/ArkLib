/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Data.MvPolynomial.NestedEvaluationTree
import ArkLib.ToCompPoly.Multilinear.Basic

/-!
  # The nested-tree zero test for computable multilinear polynomials

  This file is the CompPoly-facing view of `NestedEvaluationTree.eq_zero_of_vanishes_comp`
  (`ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean`): a computable multilinear polynomial that
  vanishes at every leaf of a sibling-distinct complete `k`-ary evaluation tree — read through a
  window of consecutive tree levels — is the zero evaluation table.

  Everything public here is stated for CompPoly's computable `CMlPolynomialEval` representation;
  Mathlib's `MvPolynomial` appears only inside the proofs, through
  `CMlPolynomialEval.eval_eq_MvPolynomial_MLE`.

  A `CMlPolynomialEval` is multilinear by construction, so `k = 2` (two distinct labels per node)
  always suffices; the statements allow any `2 ≤ k` so that a *uniformly* wider tree still certifies
  a multilinear polynomial. Note `NestedEvaluationTree` fixes one arity for every level, so this
  does not let a tree mix a `k = 2` round with a higher-degree round of the same protocol ([NOZ26]
  Lemma 9's `2 * d`, Lemma 11's `deg H + 1`); that would need per-level arity.
-/

namespace CompPoly.CMlPolynomialEval

variable {F : Type*} {k m n r : ℕ}

/-- A computable multilinear polynomial in `r` variables vanishes at every leaf point of `tree`,
each leaf point being read through the window `f` of tree levels.

The two windows used in practice are `f = Fin.castAdd` (the polynomial reads the first levels of
the tree) and `f = Fin.natAdd` (it reads the last levels), which is what lets a single transcript
tree certify two polynomials in disjoint variable blocks. -/
def PolynomialVanishes [CommRing F] (tree : NestedEvaluationTree F k n)
    (p : CMlPolynomialEval F r) (f : Fin r → Fin n) : Prop :=
  tree.Vanishes fun x => CMlPolynomialEval.eval p (Vector.ofFn (x ∘ f))

section ZeroTest

variable [Field F]

/-- **Nested-tree zero test for computable multilinear polynomials.**

If a `CMlPolynomialEval F r` evaluates to zero at every leaf of a complete `k`-ary tree of depth
`n` whose sibling labels are distinct at every node, read through the window of `r` consecutive
levels starting at level `m`, then the computable polynomial is the zero evaluation table. Later
labels may depend on the earlier path, and levels outside the window are skipped.

The statement uses only CompPoly's computable representation and evaluator. The proof transports
the table to its Mathlib multilinear extension with `eval_eq_MvPolynomial_MLE`, applies the
algebraic tree lemma `NestedEvaluationTree.eq_zero_of_vanishes_comp`, and transports the resulting
zero identity back to the table. -/
theorem eq_zero_of_polynomialVanishes_comp (hk : 2 ≤ k) (m : ℕ) (tree : NestedEvaluationTree F k n)
    (p : CMlPolynomialEval F r) (f : Fin r → Fin n) (hf : ∀ i, (f i).val = m + i.val)
    (hDistinct : tree.IsDistinct) (hVanishes : PolynomialVanishes tree p f) : p = 0 := by
  let evals : (Fin r → Fin 2) → F := fun x => p.get (finFunctionFinEquiv x)
  have hp : Vector.ofFn (fun i => evals (finFunctionFinEquiv.symm i)) = p := by
    apply Vector.ext
    intro i hi
    simp only [evals, Vector.getElem_ofFn, Equiv.apply_symm_apply]
    rfl
  have heval (x : Fin r → F) :
      CMlPolynomialEval.eval p (Vector.ofFn x) =
        MvPolynomial.eval x (MvPolynomial.MLE evals) := by
    rw [← hp]
    exact CMlPolynomialEval.eval_eq_MvPolynomial_MLE evals x
  have hMvVanishes :
      tree.Vanishes fun x => MvPolynomial.eval (x ∘ f) (MvPolynomial.MLE evals) := by
    rw [show (fun x : Fin n → F => MvPolynomial.eval (x ∘ f) (MvPolynomial.MLE evals))
        = fun x => CMlPolynomialEval.eval p (Vector.ofFn (x ∘ f)) from
      funext fun x => (heval (x ∘ f)).symm]
    exact hVanishes
  have hMvZero : MvPolynomial.MLE evals = 0 :=
    NestedEvaluationTree.eq_zero_of_vanishes_comp (by omega) tree (MvPolynomial.MLE evals) f hf
      (fun i => lt_of_le_of_lt (MvPolynomial.MLE_degreeOf evals i) (by omega)) hDistinct
      hMvVanishes
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

/-- The zero test when the polynomial reads the **first** `r` levels of the tree. -/
theorem eq_zero_of_polynomialVanishes_castAdd (hk : 2 ≤ k) {s : ℕ}
    (tree : NestedEvaluationTree F k (r + s)) (p : CMlPolynomialEval F r)
    (hDistinct : tree.IsDistinct) (hVanishes : PolynomialVanishes tree p (Fin.castAdd s)) :
    p = 0 :=
  eq_zero_of_polynomialVanishes_comp hk 0 tree p (Fin.castAdd s)
    (fun i => (Nat.zero_add i.val).symm) hDistinct hVanishes

/-- The zero test when the polynomial reads the **last** `r` levels of the tree. -/
theorem eq_zero_of_polynomialVanishes_natAdd (hk : 2 ≤ k)
    (tree : NestedEvaluationTree F k (m + r)) (p : CMlPolynomialEval F r)
    (hDistinct : tree.IsDistinct) (hVanishes : PolynomialVanishes tree p (Fin.natAdd m)) :
    p = 0 :=
  eq_zero_of_polynomialVanishes_comp hk m tree p (Fin.natAdd m) (fun _ => rfl) hDistinct hVanishes

end ZeroTest

end CompPoly.CMlPolynomialEval
