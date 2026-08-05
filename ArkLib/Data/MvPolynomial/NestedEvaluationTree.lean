/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Data.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots

/-!
  # Nested evaluation trees and their polynomial zero test

  A `NestedEvaluationTree F k n` is a complete `k`-ary tree of depth `n` whose nodes carry `k`
  scalar labels from `F`.  Labels below a node may depend on the path taken to that node, so these
  are genuine *nested* trees rather than Cartesian grids or coordinate-wise stars.  They are the
  shape of a transcript tree for `n` consecutive verifier rounds each drawing one scalar challenge
  with soundness parameter `k`.

  The main result is `NestedEvaluationTree.eq_zero_of_vanishes_comp`: if a polynomial whose
  individual degrees are all `< k` vanishes at every leaf of such a tree — read through *any* window
  of `r` consecutive tree levels — then the polynomial is zero.  The window formulation is what lets
  one
  tree certify several polynomials in disjoint variable blocks: the first `r` levels certify one,
  the last `r` levels certify another, and no tree projection or depth arithmetic is needed at the
  call site.

  Two distinct labels per node (`k = 2`) suffice for multilinear polynomials; the general `k`
  handles individual degree `≤ k - 1`.

  ## Why a tree, and not a star

  Vanishing on a coordinate-wise *star* — a center point plus, for each coordinate, further points
  differing from it in that coordinate alone — does **not** force a multilinear polynomial to
  vanish, however many points each arm carries: see
  `MvPolynomial.exists_nonzero_vanishing_on_axis_cross`. The complete tree supplies `k ^ n`
  points (`NestedEvaluationTree.numLeaves_eq_pow`) and, unlike a star, supports the interpolation
  induction below.

  ## Relation to the Cartesian-grid zero test

  `MvPolynomial.eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin`
  (`ArkLib/Data/MvPolynomial/Interpolation.lean`) is the same statement for a product set
  `∏ᵢ S i`. Neither theorem subsumes the other: the tree here allows path-dependent labels, which a
  product set cannot express, while the grid version allows a *different* root count `#(S i)` per
  variable, which a tree of uniform arity `k` cannot — picking `k` from the largest `degreeOf`
  can exceed some `#(S j)`. So the two are siblings, and what they share — the head-variable root
  count — is factored out as
  `MvPolynomial.eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero` and called by both.
  Making the grid version an actual corollary would need per-level arity here.
-/

/-- A complete `k`-ary evaluation tree of depth `n` over `F`.

Each node stores its `k` scalar challenge labels and the corresponding subtrees.  Since every child
stores its own later labels, challenges at later levels may depend on the earlier path. -/
inductive NestedEvaluationTree (F : Type*) (k : ℕ) : (n : ℕ) → Type _ where
  /-- The unique shape at depth zero. -/
  | leaf : NestedEvaluationTree F k 0
  /-- A `k`-ary challenge node followed by one subtree for each challenge. -/
  | node {n : ℕ} (challenges : Fin k → F)
      (children : Fin k → NestedEvaluationTree F k n) : NestedEvaluationTree F k (n + 1)

namespace NestedEvaluationTree

variable {F : Type*} {k m n r : ℕ}

/-- The sibling challenge labels at every node of the tree are pairwise distinct. -/
def IsDistinct : {n : ℕ} → NestedEvaluationTree F k n → Prop
  | 0, .leaf => True
  | _ + 1, .node challenges children =>
      Function.Injective challenges ∧ ∀ j, IsDistinct (children j)

/-- An evaluation function vanishes at every leaf point of an evaluation tree.

At a node, the selected challenge is prepended to the point assembled by the child.  This
recursive formulation keeps the path dependence explicit and avoids replacing the tree by a
Cartesian product. -/
def Vanishes [Zero F] : {n : ℕ} → NestedEvaluationTree F k n → ((Fin n → F) → F) → Prop
  | 0, .leaf, evalAt => evalAt (fun i => i.elim0) = 0
  | _ + 1, .node challenges children, evalAt =>
      ∀ j, Vanishes (children j) (fun x => evalAt (Fin.cons (challenges j) x))

/-! ### Transport along a depth equation

A protocol adapter that reads a tree off a transcript indexed by *rounds remaining* produces its
depth as an arithmetic expression, so the two lemmas below are occasionally needed to move
`IsDistinct` and `Vanishes` across a depth equation.  Nothing in the zero test itself needs them:
the window formulation of `eq_zero_of_vanishes_comp` is what removes the depth arithmetic that
would otherwise arise from projecting a tree onto a prefix or a suffix. -/

@[simp]
theorem isDistinct_cast {m : ℕ} (h : n = m) (tree : NestedEvaluationTree F k n) :
    (h ▸ tree).IsDistinct ↔ tree.IsDistinct := by
  subst h
  rfl

@[simp]
theorem vanishes_cast [Zero F] {m : ℕ} (h : n = m) (tree : NestedEvaluationTree F k n)
    (evalAt : (Fin m → F) → F) :
    (h ▸ tree).Vanishes evalAt ↔
      tree.Vanishes (fun x => evalAt fun i => x (Fin.cast h.symm i)) := by
  subst h
  rfl

/-- The number of leaves of an evaluation tree, i.e. the number of transcripts an extractor
consuming it must be handed. -/
def numLeaves : {n : ℕ} → NestedEvaluationTree F k n → ℕ
  | 0, .leaf => 1
  | _ + 1, .node _ children => ∑ j, numLeaves (children j)

/-- A complete `k`-ary tree of depth `n` has exactly `k ^ n` leaves.  Together with the arity pins
of a concrete protocol this is what bounds the size of the transcript tree its extractor
consumes. -/
theorem numLeaves_eq_pow (tree : NestedEvaluationTree F k n) : tree.numLeaves = k ^ n := by
  induction tree with
  | leaf => simp [numLeaves]
  | node challenges children ih =>
      simp only [numLeaves, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, pow_succ, mul_comm]

/-- An index whose value is a successor is the `Fin.succ` of the corresponding index. -/
private theorem eq_succ_of_val_eq_succ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}
    (h : i.val = j.val + 1) : i = j.succ :=
  Fin.ext (by simpa using h)

section ZeroTest

variable [CommRing F] [IsDomain F]

/-- **Nested-tree zero test.**

Let `tree` be a complete `k`-ary evaluation tree of depth `n` with pairwise-distinct sibling
labels, and let `p` be a polynomial in `r` variables whose individual degrees are all `< k`.  Read
each leaf point through a window `f` of `r` consecutive tree levels starting at level `m`, i.e.
`(f i).val = m + i.val`.  If `p` vanishes at every windowed leaf point then `p = 0`.

Later labels may depend on the earlier path, and levels outside the window are simply skipped —
so one tree certifies a separate polynomial for each variable block, with no tree projection and
no depth subtraction.  The two cases used in practice are `f = Fin.castAdd` (the polynomial reads
the first `r` levels) and `f = Fin.natAdd` (it reads the last `r` levels).

The proof is a single induction on the tree.  At a level inside the window, fixing the first
variable preserves the degree bound for every remaining variable, so the induction hypothesis makes
all `k` restricted polynomials zero; the `k` distinct sibling labels are then `k` roots against
degree `< k` in that variable, which is
`MvPolynomial.eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero` (shared with the Cartesian-grid
zero test).  At a level outside the window the proof simply descends into one child. -/
theorem eq_zero_of_vanishes_comp (hk : 0 < k) {n : ℕ} (tree : NestedEvaluationTree F k n)
    {m r : ℕ} (p : MvPolynomial (Fin r) F) (f : Fin r → Fin n)
    (hf : ∀ i, (f i).val = m + i.val) (hDegree : ∀ i, p.degreeOf i < k)
    (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval (x ∘ f) p) : p = 0 := by
  classical
  revert m r p f hf hDegree hDistinct hVanishes
  induction tree with
  | leaf =>
      intro m r p f hf _ _ hVanishes
      match r with
      | 0 =>
          rw [MvPolynomial.eq_C_of_isEmpty p] at hVanishes ⊢
          simpa [Vanishes] using hVanishes
      | _ + 1 => exact (f 0).elim0
  | @node n challenges children ih =>
      intro m r p f hf hDegree hDistinct hVanishes
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
        have h0 : (children ⟨0, hk⟩).Vanishes fun y =>
            MvPolynomial.eval ((Fin.cons (challenges ⟨0, hk⟩) y : Fin (n + 1) → F) ∘ f) p :=
          hVanishes ⟨0, hk⟩
        have hfun : (fun y : Fin n → F =>
              MvPolynomial.eval ((Fin.cons (challenges ⟨0, hk⟩) y : Fin (n + 1) → F) ∘ f) p)
            = fun y => MvPolynomial.eval (y ∘ fun i => (⟨m' + i.val, hlt i⟩ : Fin n)) p := by
          funext y
          refine congrArg (MvPolynomial.eval · p) (funext fun i => ?_)
          simp only [Function.comp_apply, hfi i, Fin.cons_succ]
        rw [hfun] at h0
        exact ih ⟨0, hk⟩ (m := m') p _ (fun _ => rfl) hDegree (hChildren _) h0
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
            exact ih j (m := 0) _ _ (fun i => (Nat.zero_add i.val).symm)
              (fun i => lt_of_le_of_lt
                (MvPolynomial.degreeOf_eval_C_finSuccEquiv p i (challenges j)) (hDegree i.succ))
              (hChildren j) h1
          -- `k` distinct roots against degree `< k` in the head variable — the step shared with
          -- the Cartesian-grid zero test `eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin`.
          have hCard : (Finset.univ.image challenges).card = k := by
            rw [Finset.card_image_of_injective _ hChallenges, Finset.card_univ, Fintype.card_fin]
          refine MvPolynomial.eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero
            (Finset.univ.image challenges) (by rw [hCard]; exact hDegree 0) ?_
          intro x hx
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
          exact hRestrictedZero j

/-- The zero test in the common case where the polynomial reads the *first* `r` levels of the
tree. -/
theorem eq_zero_of_vanishes_castAdd (hk : 0 < k) {r s : ℕ}
    (tree : NestedEvaluationTree F k (r + s)) (p : MvPolynomial (Fin r) F)
    (hDegree : ∀ i, p.degreeOf i < k) (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval (x ∘ Fin.castAdd s) p) : p = 0 :=
  eq_zero_of_vanishes_comp hk tree p (Fin.castAdd s) (fun i => (Nat.zero_add i.val).symm)
    hDegree hDistinct hVanishes

/-- The zero test in the common case where the polynomial reads the *last* `r` levels of the
tree. -/
theorem eq_zero_of_vanishes_natAdd (hk : 0 < k) {m r : ℕ}
    (tree : NestedEvaluationTree F k (m + r)) (p : MvPolynomial (Fin r) F)
    (hDegree : ∀ i, p.degreeOf i < k) (hDistinct : tree.IsDistinct)
    (hVanishes : tree.Vanishes fun x => MvPolynomial.eval (x ∘ Fin.natAdd m) p) : p = 0 :=
  eq_zero_of_vanishes_comp hk tree p (Fin.natAdd m) (fun _ => rfl) hDegree hDistinct hVanishes

end ZeroTest

end NestedEvaluationTree
