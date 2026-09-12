/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Combinatorics.Quiver.Schreier
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The labelled Gabber–Galil graph

The eight affine maps on `(ZMod m)²` are the maps in Construction 8.1 of
Hoory–Linial–Wigderson, *Expander graphs and their applications* (2006):
<https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/HLW06/hlw06.pdf>.
This is the standard graph used by `alg:paired-candidates` in the decoder paper.

The semantic graph reuses Mathlib's `Quiver.SchreierGraph`. Each label specifies
one outgoing dart, including loops and parallel darts. In particular, forming a
set of neighboring vertices would not preserve this graph. Reversing a dart swaps
its paired label; a loop still has two distinct orientations.

This module proves regularity and reverse-edge correspondence. It does not yet
prove a spectral bound, graph powering, or the decoder's independent-selection
claim.
-/

@[expose] public section

namespace GabberGalil

/-- Coordinates modulo the side length; finite graphs use a positive side length. -/
abbrev Vertex (m : ℕ) := ZMod m × ZMod m

/-- Eight distinct outgoing labels, paired consecutively with their reversals. -/
abbrev Label := Fin 8

/-- Reverse the orientation label without identifying equal endpoint pairs. -/
def reverseLabel : Label → Label := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- Execute one of the eight affine maps. This needs no primality assumption. -/
def step {m : ℕ} (l : Label) (v : Vertex m) : Vertex m :=
  ![(v.1 + 2 * v.2, v.2), (v.1 - 2 * v.2, v.2),
    (v.1 + (2 * v.2 + 1), v.2), (v.1 - (2 * v.2 + 1), v.2),
    (v.1, v.2 + 2 * v.1), (v.1, v.2 - 2 * v.1),
    (v.1, v.2 + (2 * v.1 + 1)), (v.1, v.2 - (2 * v.1 + 1))] l

@[simp] theorem reverseLabel_reverseLabel (l : Label) :
    reverseLabel (reverseLabel l) = l := by
  fin_cases l <;> rfl

theorem reverseLabel_ne (l : Label) : reverseLabel l ≠ l := by
  fin_cases l <;> decide

/-- Reversing an executed dart returns to its original vertex. -/
@[simp] theorem step_reverse {m : ℕ} (l : Label) (v : Vertex m) :
    step (reverseLabel l) (step l v) = v := by
  rcases v with ⟨x, y⟩
  fin_cases l <;> simp [step, reverseLabel]

/-- Each labelled map is a permutation, with its explicit paired inverse. -/
def stepPerm (m : ℕ) (l : Label) : Equiv.Perm (Vertex m) where
  toFun := step l
  invFun := step (reverseLabel l)
  left_inv := step_reverse l
  right_inv v := by simpa using step_reverse (reverseLabel l) v

/-- The existing labelled multigraph owner specialized to the eight affine maps. -/
abbrev Graph (m : ℕ) := Quiver.SchreierGraph (Vertex m) (stepPerm m)

/-- The finite square grid has exactly `m²` vertices for every positive side length. -/
theorem vertex_card (m : ℕ) [NeZero m] : Nat.card (Vertex m) = m ^ 2 := by
  simp [Vertex, Nat.card_eq_fintype_card, ZMod.card, pow_two]

/-- Wrapping coordinates in the semantic graph does not change the vertex count. -/
theorem graph_card (m : ℕ) [NeZero m] : Nat.card (Graph m) = m ^ 2 := by
  rw [← Nat.card_congr (Quiver.SchreierGraph.equiv (Vertex m) (stepPerm m))]
  exact vertex_card m

/-- The executable neighbor list retains all eight labels, even at coinciding endpoints. -/
def neighbors {m : ℕ} (v : Vertex m) : List (Vertex m) := List.ofFn (step · v)

@[simp] theorem neighbors_length {m : ℕ} (v : Vertex m) :
    (neighbors v).length = 8 := by simp [neighbors]

/-- The label-to-star equivalence witnesses degree eight in the semantic multigraph. -/
def starEquiv {m : ℕ} (v : Graph m) : Quiver.Star v ≃ Label where
  toFun e := e.2.val
  invFun l := ⟨(stepPerm m l) • v, l, rfl⟩
  left_inv := by rintro ⟨w, l, rfl⟩; rfl
  right_inv _ := rfl

/-- Every vertex has eight outgoing darts, with loops and multiplicities included. -/
theorem regular {m : ℕ} (v : Graph m) : Nat.card (Quiver.Star v) = 8 := by
  rw [Nat.card_congr (starEquiv v), Nat.card_eq_fintype_card]
  rfl

/-- Edge reversal acts on labelled darts, not on mere endpoint adjacency. -/
def reverseEdge {m : ℕ} {v w : Graph m} (e : v ⟶ w) : w ⟶ v :=
  ⟨reverseLabel e.val, by
    have h := congrArg Quiver.SchreierGraph.toVertex e.property
    change step e.val v.toVertex = w.toVertex at h
    apply Quiver.SchreierGraph.ext
    change step (reverseLabel e.val) w.toVertex = v.toVertex
    rw [← h, step_reverse]⟩

@[simp] theorem reverseEdge_reverseEdge {m : ℕ} {v w : Graph m} (e : v ⟶ w) :
    reverseEdge (reverseEdge e) = e := by
  apply Subtype.ext
  exact reverseLabel_reverseLabel e.val

/-- A bijection of opposite directed edge fibers, preserving parallel-edge counts. -/
def edgeReverseEquiv {m : ℕ} (v w : Graph m) : (v ⟶ w) ≃ (w ⟶ v) where
  toFun := reverseEdge
  invFun := reverseEdge
  left_inv := reverseEdge_reverseEdge
  right_inv := reverseEdge_reverseEdge

/-- Opposite endpoint pairs have the same multiplicity. -/
theorem edgeMultiplicity_symm {m : ℕ} (v w : Graph m) :
    Nat.card (v ⟶ w) = Nat.card (w ⟶ v) :=
  Nat.card_congr (edgeReverseEquiv v w)

end GabberGalil
