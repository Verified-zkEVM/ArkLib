/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.MvPolynomial.NestedEvaluationTree
public import VCVio.CryptoFoundations.Rewinding.Finder

/-!
  # Challenge trees of the rewinding finders as nested evaluation trees

  The black-box finders of `VCVio.CryptoFoundations.Rewinding` return a `Rewinding.VecTree`: a
  challenge vector for each branch path, whose challenge at a round depends only on the path
  through that round. When every round has a scalar challenge in a field `F`, such a tree is a
  nested evaluation tree (`NestedEvaluationTree F n k`): below each branch of the first round
  hangs the tree of the later rounds.

  ## Main definitions

  - `Rewinding.VecTree.toNested`: the nested evaluation tree of a challenge tree with at least one
    branch per round.
  - `Rewinding.VecTree.isDistinct_toNested`, `Rewinding.VecTree.vanishes_toNested`: its sibling
    labels are distinct when the challenge tree is structured by injectivity, and an evaluation
    function vanishes on it exactly when it vanishes at every leaf of the challenge tree.
  - `Rewinding.VecTree.eq_zero_of_vanishes`: a polynomial whose individual degree in the variable
    of round `i` is below the number of branches `k i` of that round is zero if it vanishes at
    every leaf of a challenge tree with distinct siblings.
-/

@[expose] public section

namespace Rewinding

namespace VecTree

variable {F : Type}

/-- The subtree of a challenge tree below the branch `j` of its first round: the later rounds,
with the first choice fixed to `j`. -/
def tail {n : ℕ} {k : Fin (n + 1) → ℕ} (t : VecTree (fun _ : Fin (n + 1) => F) k)
    (j : Fin (k 0)) : VecTree (fun _ : Fin n => F) (Fin.tail k) where
  leaf q r := t.leaf (Fin.cons j q) r.succ
  causal p p' r h := by
    refine t.causal _ _ r.succ fun s hs => ?_
    cases s using Fin.cases with
    | zero => rfl
    | succ s => exact h s (Fin.succ_le_succ_iff.mp hs)

/-- The challenge of the first round on the branch `j`: it does not depend on the later choices,
which are taken to be the first branches. -/
def root {n : ℕ} {k : Fin (n + 1) → ℕ} (hk : ∀ i, 0 < k i)
    (t : VecTree (fun _ : Fin (n + 1) => F) k) (j : Fin (k 0)) : F :=
  t.leaf (Fin.cons j fun r => ⟨0, hk r.succ⟩) 0

theorem leaf_cons_zero {n : ℕ} {k : Fin (n + 1) → ℕ} (hk : ∀ i, 0 < k i)
    (t : VecTree (fun _ : Fin (n + 1) => F) k) (j : Fin (k 0)) (q : (i : Fin n) → Fin (k i.succ)) :
    t.leaf (Fin.cons j q) 0 = t.root hk j :=
  t.causal _ _ 0 fun s hs => by
    obtain rfl : s = 0 := Fin.le_zero_iff.mp hs
    rfl

theorem leaf_cons {n : ℕ} {k : Fin (n + 1) → ℕ} (hk : ∀ i, 0 < k i)
    (t : VecTree (fun _ : Fin (n + 1) => F) k) (j : Fin (k 0)) (q : (i : Fin n) → Fin (k i.succ)) :
    t.leaf (Fin.cons j q) = Fin.cons (t.root hk j) ((t.tail j).leaf q) := by
  funext r
  cases r using Fin.cases with
  | zero => exact t.leaf_cons_zero hk j q
  | succ r => rfl

/-- The nested evaluation tree of a challenge tree with at least one branch per round. -/
def toNested : {n : ℕ} → {k : Fin n → ℕ} → (∀ i, 0 < k i) →
    VecTree (fun _ : Fin n => F) k → NestedEvaluationTree F n k
  | 0, _, _, _ => .leaf
  | _ + 1, _, hk, t => .node (t.root hk) fun j => toNested (fun i => hk i.succ) (t.tail j)

/-- The sibling labels of the nested tree of a structured challenge tree are distinct. -/
theorem isDistinct_toNested {n : ℕ} {k : Fin n → ℕ} (hk : ∀ i, 0 < k i)
    (t : VecTree (fun _ : Fin n => F) k)
    (ht : t.IsStructured fun _ ch => Function.Injective ch) : (toNested hk t).IsDistinct := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, fun j => ih (fun i => hk i.succ) (t.tail j) fun q r => ?_⟩
      · have h := ht (Fin.cons ⟨0, hk 0⟩ fun r => ⟨0, hk r.succ⟩) 0
        have hfun : t.siblings (Fin.cons ⟨0, hk 0⟩ fun r => ⟨0, hk r.succ⟩) 0 = t.root hk := by
          funext j
          simp only [VecTree.siblings]
          rw [Fin.update_cons_zero, leaf_cons_zero]
        rw [hfun] at h
        exact h
      · have h := ht (Fin.cons j q) r.succ
        have hfun : (t.tail j).siblings q r = t.siblings (Fin.cons j q) r.succ := by
          funext i
          exact congrArg (fun p => t.leaf p r.succ)
            (Fin.cons_update (α := fun s => Fin (k s)) j q r i)
        intro a b hab
        exact h (((congrFun hfun a).symm.trans hab).trans (congrFun hfun b))

/-- An evaluation function vanishes on the nested tree of a challenge tree exactly when it
vanishes at every leaf of the challenge tree. -/
theorem vanishes_toNested [Zero F] {n : ℕ} {k : Fin n → ℕ} (hk : ∀ i, 0 < k i)
    (t : VecTree (fun _ : Fin n => F) k) (evalAt : (Fin n → F) → F) :
    (toNested hk t).Vanishes evalAt ↔ ∀ path, evalAt (t.leaf path) = 0 := by
  induction n with
  | zero =>
      have hleaf : ∀ path, t.leaf path = fun i : Fin 0 => i.elim0 := fun path =>
        funext fun i => i.elim0
      refine ⟨fun h path => ?_, fun h => ?_⟩
      · rw [hleaf path]
        exact h
      · have h' := h fun i => i.elim0
        rw [hleaf] at h'
        exact h'
  | succ n ih =>
      rw [Fin.forall_fin_succ_pi]
      refine forall_congr' fun j => ?_
      refine (ih (fun i => hk i.succ) (t.tail j) _).trans (forall_congr' fun q => ?_)
      rw [leaf_cons hk]

section ZeroTest

variable [CommRing F] [IsDomain F]

/-- **Interpolation on a challenge tree.** A polynomial whose individual degree in the variable of
round `i` is below the number `k i` of branches of that round is zero if it vanishes at every leaf
of a challenge tree whose siblings are distinct at every node. -/
theorem eq_zero_of_vanishes {n : ℕ} {k : Fin n → ℕ}
    (t : VecTree (fun _ : Fin n => F) k)
    (ht : t.IsStructured fun _ ch => Function.Injective ch) (p : MvPolynomial (Fin n) F)
    (hDegree : ∀ i, p.degreeOf i < k i)
    (hVanishes : ∀ path, MvPolynomial.eval (t.leaf path) p = 0) : p = 0 :=
  have hk : ∀ i, 0 < k i := fun i => (Nat.zero_le _).trans_lt (hDegree i)
  NestedEvaluationTree.eq_zero_of_vanishes_comp hk (toNested hk t) p id
    (fun _ => (Nat.zero_add _).symm) hDegree (isDistinct_toNested hk t ht)
    ((vanishes_toNested hk t _).2 hVanishes)

end ZeroTest

end VecTree

end Rewinding
