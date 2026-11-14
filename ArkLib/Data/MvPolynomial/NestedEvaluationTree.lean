/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import ArkLib.Data.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Roots

/-!
  # Nested evaluation trees and their polynomial zero test

  A `NestedEvaluationTree F n k` is a complete tree of depth `n` over `F` whose nodes at level `i`
  carry `k i` scalar labels.  Labels below a node may depend on the path taken to that node, so
  these are genuine *nested* trees rather than Cartesian grids or coordinate-wise stars.  They are
  the shape of a transcript tree for `n` consecutive verifier rounds, each drawing one scalar
  challenge with soundness parameter `k i`.  A constant arity `fun _ => k` is the common case.

  The main result is `NestedEvaluationTree.eq_zero_of_vanishes_comp`: if a polynomial whose
  individual degree in the variable read at level `i` is `< k i` vanishes at every leaf of such a
  tree — read through *any* window of `r` consecutive tree levels — then the polynomial is zero.
  The window formulation is what lets one tree certify several polynomials in disjoint variable
  blocks: the first `r` levels certify one, the last `r` levels certify another, and no tree
  projection or depth arithmetic is needed at the call site.

  Two distinct labels per node (`k i = 2`) suffice for a multilinear variable; in general
  `k i` labels handle individual degree `≤ k i - 1`, and different levels may use different
  arities.

  ## Why a tree, and not a star

  Vanishing on a coordinate-wise *star* — a center point plus, for each coordinate, further points
  differing from it in that coordinate alone — does **not** force a multilinear polynomial to
  vanish, however many points each arm carries: see
  `MvPolynomial.exists_nonzero_vanishing_on_axis_cross`. The complete tree supplies `∏ i, k i`
  points (`NestedEvaluationTree.numLeaves_eq_prod`) and, unlike a star, supports the interpolation
  induction below.

  ## Relation to the Cartesian-grid zero test

  `MvPolynomial.eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin`
  (`ArkLib/Data/MvPolynomial/Interpolation.lean`) is the same statement for a product set
  `∏ᵢ S i`.  A product set is a nested tree whose labels do not depend on the path and whose arity
  at level `i` is `#(S i)`, so the per-level arity here makes the grid test a corollary:
  `NestedEvaluationTree.grid` is that tree and the grid test is derived from
  `NestedEvaluationTree.eq_zero_of_vanishes_comp` in `Interpolation.lean`.  The head-variable root
  count shared by both is
  `MvPolynomial.eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero`.
-/

@[expose] public section

/-- A complete evaluation tree of depth `n` over `F`, with `k i` branches at level `i`.

Each node stores its scalar challenge labels and one subtree for each of them.  Since every child
stores its own later labels, challenges at later levels may depend on the earlier path. -/
inductive NestedEvaluationTree (F : Type*) : (n : ℕ) → (Fin n → ℕ) → Type _ where
  /-- The unique shape at depth zero. -/
  | leaf {k : Fin 0 → ℕ} : NestedEvaluationTree F 0 k
  /-- A node with `k 0` challenge labels followed by one subtree for each label. -/
  | node {n : ℕ} {k : Fin (n + 1) → ℕ} (challenges : Fin (k 0) → F)
      (children : Fin (k 0) → NestedEvaluationTree F n (Fin.tail k)) :
      NestedEvaluationTree F (n + 1) k

namespace NestedEvaluationTree

variable {F : Type*} {m n r : ℕ}

/-- The sibling challenge labels at every node of the tree are pairwise distinct. -/
def IsDistinct : {n : ℕ} → {k : Fin n → ℕ} → NestedEvaluationTree F n k → Prop
  | 0, _, .leaf => True
  | _ + 1, _, .node challenges children =>
      Function.Injective challenges ∧ ∀ j, IsDistinct (children j)

/-- An evaluation function vanishes at every leaf point of an evaluation tree.

At a node, the selected challenge is prepended to the point assembled by the child.  This
recursive formulation keeps the path dependence explicit and avoids replacing the tree by a
Cartesian product. -/
def Vanishes [Zero F] :
    {n : ℕ} → {k : Fin n → ℕ} → NestedEvaluationTree F n k → ((Fin n → F) → F) → Prop
  | 0, _, .leaf, evalAt => evalAt (fun i => i.elim0) = 0
  | _ + 1, _, .node challenges children, evalAt =>
      ∀ j, Vanishes (children j) (fun x => evalAt (Fin.cons (challenges j) x))

/-! ### Transport along a depth equation

A protocol adapter that reads a tree off a transcript indexed by *rounds remaining* produces its
depth as an arithmetic expression, so the two lemmas below are occasionally needed to move
`IsDistinct` and `Vanishes` across a depth equation of a tree with a constant arity.  Nothing in the
zero test itself needs them: the window formulation of `eq_zero_of_vanishes_comp` is what removes
the depth arithmetic that would otherwise arise from projecting a tree onto a prefix or a
suffix. -/

@[simp]
theorem isDistinct_cast {k : ℕ} {m : ℕ} (h : n = m) (tree : NestedEvaluationTree F n fun _ => k) :
    (h ▸ tree : NestedEvaluationTree F m fun _ => k).IsDistinct ↔ tree.IsDistinct := by
  subst h
  rfl

@[simp]
theorem vanishes_cast [Zero F] {k : ℕ} {m : ℕ} (h : n = m)
    (tree : NestedEvaluationTree F n fun _ => k) (evalAt : (Fin m → F) → F) :
    (h ▸ tree : NestedEvaluationTree F m fun _ => k).Vanishes evalAt ↔
      tree.Vanishes (fun x => evalAt fun i => x (Fin.cast h.symm i)) := by
  subst h
  rfl

/-- The number of leaves of an evaluation tree, i.e. the number of transcripts an extractor
consuming it must be handed. -/
def numLeaves : {n : ℕ} → {k : Fin n → ℕ} → NestedEvaluationTree F n k → ℕ
  | 0, _, .leaf => 1
  | _ + 1, _, .node _ children => ∑ j, numLeaves (children j)

/-- A complete tree has exactly `∏ i, k i` leaves.  Together with the arity pins of a concrete
protocol this is what bounds the size of the transcript tree its extractor consumes. -/
theorem numLeaves_eq_prod {k : Fin n → ℕ} (tree : NestedEvaluationTree F n k) :
    tree.numLeaves = ∏ i, k i := by
  induction tree with
  | leaf => simp [numLeaves]
  | node challenges children ih =>
      simp only [numLeaves, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, Fin.prod_univ_succ]
      rfl

/-- A tree with the same arity `k` at every level has exactly `k ^ n` leaves. -/
theorem numLeaves_eq_pow {k : ℕ} (tree : NestedEvaluationTree F n fun _ => k) :
    tree.numLeaves = k ^ n := by
  rw [numLeaves_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Path-independent labels: Cartesian grids

A product set is the tree whose labels at level `i` come from one list `label i` and do not depend
on the path.  This is how the Cartesian-grid zero test is a corollary of the nested one. -/

/-- The tree whose level `i` carries the labels `label i` below every node. -/
def grid : {n : ℕ} → {k : Fin n → ℕ} → ((i : Fin n) → Fin (k i) → F) →
    NestedEvaluationTree F n k
  | 0, _, _ => .leaf
  | _ + 1, _, label => .node (label 0) fun _ => grid fun i => label i.succ

/-- The sibling labels of a grid are distinct when each level's labels are. -/
theorem isDistinct_grid {k : Fin n → ℕ} (label : (i : Fin n) → Fin (k i) → F)
    (h : ∀ i, Function.Injective (label i)) : (grid label).IsDistinct := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨h 0, fun _ => ih _ fun i => h i.succ⟩

/-- An evaluation function vanishes on a grid exactly when it vanishes at every choice of one
label per level. -/
theorem vanishes_grid [Zero F] {k : Fin n → ℕ} (label : (i : Fin n) → Fin (k i) → F)
    (evalAt : (Fin n → F) → F) :
    (grid label).Vanishes evalAt ↔ ∀ path : (i : Fin n) → Fin (k i),
      evalAt (fun i => label i (path i)) = 0 := by
  induction n with
  | zero =>
      simp only [grid, Vanishes]
      refine ⟨fun h path => ?_, fun h => ?_⟩
      · rw [show (fun i => label i (path i)) = fun i : Fin 0 => i.elim0 from
          funext fun i => i.elim0]
        exact h
      · convert h fun i => i.elim0 using 2
  | succ n ih =>
      simp only [grid, Vanishes]
      rw [Fin.forall_fin_succ_pi]
      refine forall_congr' fun j => ?_
      refine (ih (fun i => label i.succ) _).trans ?_
      refine forall_congr' fun path => ?_
      refine Eq.congr_left (congrArg evalAt (funext fun i => ?_))
      refine Fin.cases ?_ (fun i => ?_) i <;> simp

section ZeroTest

variable [CommRing F] [IsDomain F]

/-- **Nested-tree zero test.**

Let `tree` be a complete evaluation tree of depth `n` with `k i` pairwise-distinct sibling labels
at level `i`, and let `p` be a polynomial in `r` variables.  Read each leaf point through a window
`f` of `r` consecutive tree levels starting at level `m`, i.e. `(f i).val = m + i.val`, and suppose
the individual degree of `p` in variable `i` is `< k (f i)`.  If `p` vanishes at every windowed leaf
point then `p = 0`.  Every level needs at least one label, including those outside the window,
because a level without labels leaves the tree without leaves.

Later labels may depend on the earlier path, and levels outside the window are simply skipped —
so one tree certifies a separate polynomial for each variable block, with no tree projection and
no depth subtraction.  The two cases used in practice are `f = Fin.castAdd` (the polynomial reads
the first `r` levels) and `f = Fin.natAdd` (it reads the last `r` levels).

The proof is a single induction on the tree.  At a level inside the window, fixing the first
variable preserves the degree bound for every remaining variable, so the induction hypothesis makes
all `k 0` restricted polynomials zero; the `k 0` distinct sibling labels are then `k 0` roots
against degree `< k 0` in that variable, which is
`MvPolynomial.eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero`.  At a level outside the window
the proof simply descends into one child. -/
theorem eq_zero_of_vanishes_comp {n : ℕ} {k : Fin n → ℕ} (hk : ∀ i, 0 < k i)
    (tree : NestedEvaluationTree F n k)
    {m r : ℕ} (p : MvPolynomial (Fin r) F) (f : Fin r → Fin n)
    (hf : ∀ i, (f i).val = m + i.val) (hDegree : ∀ i, p.degreeOf i < k (f i))
    (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval (x ∘ f) p) : p = 0 := by
  classical
  revert hk m r p f hf hDegree hDistinct hVanishes
  induction tree with
  | leaf =>
      intro _ m r p f hf _ _ hVanishes
      match r with
      | 0 =>
          rw [MvPolynomial.eq_C_of_isEmpty p] at hVanishes ⊢
          simpa [Vanishes] using hVanishes
      | _ + 1 => exact (f 0).elim0
  | @node n k challenges children ih =>
      intro hk m r p f hf hDegree hDistinct hVanishes
      obtain ⟨hChallenges, hChildren⟩ := hDistinct
      -- Outside the window, or with nothing left to certify: descend into the first child.
      have descend : ∀ m' : ℕ, (∀ i : Fin r, (f i).val = m' + 1 + i.val) → p = 0 := by
        intro m' hf'
        have hlt : ∀ i : Fin r, m' + i.val < n := fun i => by
          have h := (f i).isLt
          rw [hf' i] at h
          omega
        have hfi : ∀ i : Fin r, f i = Fin.succ ⟨m' + i.val, hlt i⟩ := fun i => by
          apply Fin.ext
          simp only [Fin.val_succ, hf' i]
          omega
        have h0 : (children ⟨0, hk 0⟩).Vanishes fun y =>
            MvPolynomial.eval ((Fin.cons (challenges ⟨0, hk 0⟩) y : Fin (n + 1) → F) ∘ f) p :=
          hVanishes ⟨0, hk 0⟩
        have hfun : (fun y : Fin n → F =>
              MvPolynomial.eval
                ((Fin.cons (challenges ⟨0, hk 0⟩) y : Fin (n + 1) → F) ∘ f) p)
            = fun y => MvPolynomial.eval (y ∘ fun i => (⟨m' + i.val, hlt i⟩ : Fin n)) p := by
          funext y
          refine congrArg (MvPolynomial.eval · p) (funext fun i => ?_)
          simp only [Function.comp_apply, hfi i, Fin.cons_succ]
        rw [hfun] at h0
        exact ih ⟨0, hk 0⟩ (fun i => hk i.succ) (m := m') p _ (fun _ => rfl)
          (fun i => by have h := hDegree i; rw [hfi i] at h; exact h) (hChildren _) h0
      match m, r with
      | m' + 1, _ => exact descend m' (by simpa [Nat.add_assoc] using hf)
      | 0, 0 => exact descend 0 (fun i => i.elim0)
      | 0, r' + 1 =>
          -- Inside the window: the head level feeds variable `0` of `p`.
          have hlt : ∀ i : Fin r', i.val < n := fun i => by
            have h := (f i.succ).isLt
            rw [hf i.succ] at h
            simp only [Fin.val_succ] at h
            omega
          have hf0 : f 0 = 0 := Fin.ext (by simpa using hf 0)
          have hfsucc : ∀ i : Fin r', f i.succ = Fin.succ ⟨i.val, hlt i⟩ := fun i => by
            apply Fin.ext
            simp only [Fin.val_succ, hf i.succ]
            omega
          have hRestrictedZero : ∀ j, Polynomial.eval (MvPolynomial.C (challenges j))
              (MvPolynomial.finSuccEquiv F r' p) = 0 := by
            intro j
            have h1 : (children j).Vanishes fun y =>
                MvPolynomial.eval ((Fin.cons (challenges j) y : Fin (n + 1) → F) ∘ f) p :=
              hVanishes j
            have hfun : (fun y : Fin n → F =>
                  MvPolynomial.eval ((Fin.cons (challenges j) y : Fin (n + 1) → F) ∘ f) p)
                = fun y => MvPolynomial.eval (y ∘ fun i => (⟨i.val, hlt i⟩ : Fin n))
                  (Polynomial.eval (MvPolynomial.C (challenges j))
                    (MvPolynomial.finSuccEquiv F r' p)) := by
              funext y
              rw [MvPolynomial.eval_comp_eval_C_finSuccEquiv]
              refine congrArg (MvPolynomial.eval · p) (funext fun i => ?_)
              refine Fin.cases ?_ (fun i' => ?_) i
              · simp only [Function.comp_apply, hf0, Fin.cons_zero]
              · simp only [Function.comp_apply, hfsucc i', Fin.cons_succ, Function.comp_apply]
            rw [hfun] at h1
            exact ih j (fun i => hk i.succ) (m := 0) _ _ (fun i => (Nat.zero_add i.val).symm)
              (fun i => lt_of_le_of_lt
                (MvPolynomial.degreeOf_eval_C_finSuccEquiv p i (challenges j))
                (by have h := hDegree i.succ; rw [hfsucc i] at h; exact h))
              (hChildren j) h1
          -- `k 0` distinct roots against degree `< k 0` in the head variable.
          have hCard : (Finset.univ.image challenges).card = k 0 := by
            rw [Finset.card_image_of_injective _ hChallenges, Finset.card_univ, Fintype.card_fin]
          refine MvPolynomial.eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero
            (Finset.univ.image challenges) (by rw [hCard]; simpa only [hf0] using hDegree 0) ?_
          intro x hx
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
          exact hRestrictedZero j

/-- The zero test in the common case where the polynomial reads the *first* `r` levels of the
tree. -/
theorem eq_zero_of_vanishes_castAdd {r s : ℕ} {k : Fin (r + s) → ℕ} (hk : ∀ i, 0 < k i)
    (tree : NestedEvaluationTree F (r + s) k) (p : MvPolynomial (Fin r) F)
    (hDegree : ∀ i, p.degreeOf i < k (Fin.castAdd s i)) (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval (x ∘ Fin.castAdd s) p) : p = 0 :=
  eq_zero_of_vanishes_comp hk tree p (Fin.castAdd s) (fun i => (Nat.zero_add i.val).symm)
    hDegree hDistinct hVanishes

/-- The zero test in the common case where the polynomial reads the *last* `r` levels of the
tree. -/
theorem eq_zero_of_vanishes_natAdd {m r : ℕ} {k : Fin (m + r) → ℕ} (hk : ∀ i, 0 < k i)
    (tree : NestedEvaluationTree F (m + r) k) (p : MvPolynomial (Fin r) F)
    (hDegree : ∀ i, p.degreeOf i < k (Fin.natAdd m i)) (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval (x ∘ Fin.natAdd m) p) : p = 0 :=
  eq_zero_of_vanishes_comp hk tree p (Fin.natAdd m) (fun _ => rfl) hDegree hDistinct hVanishes

end ZeroTest

end NestedEvaluationTree
