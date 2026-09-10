/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Expected authentication boundaries under uniform queries

A Merkle multiproof contains one authentication hash for an empty subtree whose sibling contains
at least one queried leaf.  This module proves the elementary finite counting identity behind the
expected number of such hashes.  Queries are independent and uniform because the sample space is
the full function type `Fin t -> alpha`, equipped with counting measure.

The theorem is stated for an arbitrary finite family of oriented sibling boundaries.  A binary
tree is obtained by taking one node for every subtree at every non-root level.  The proof depends
only on the cardinalities of a subtree and its union with its sibling, so a later numerical model
can use the usual sizes `2^j` and `2^(j+1)` without formalizing a deployed Merkle serializer.
-/

@[expose] public section

namespace ArkLib.UniformQueryBoundary

open scoped BigOperators

noncomputable section

/-- A query tuple misses every element of `S`. -/
abbrev QueriesAvoid {alpha : Type*} [DecidableEq alpha] {t : ℕ}
    (S : Finset alpha) (queries : Fin t → alpha) : Prop :=
  ∀ i, queries i ∉ S

/-- The oriented authentication-boundary event: the subtree is empty and its sibling is not. -/
abbrev IsAuthenticationBoundary {alpha : Type*} [DecidableEq alpha] {t : ℕ}
    (subtree sibling : Finset alpha) (queries : Fin t → alpha) : Prop :=
  QueriesAvoid subtree queries ∧ ¬QueriesAvoid sibling queries

/-- Number of oriented authentication boundaries exposed by a query tuple. -/
def authenticationHashCount {alpha node : Type*} [Fintype node] [DecidableEq alpha]
    {t : ℕ} (subtree sibling : node → Finset alpha) (queries : Fin t → alpha) : ℕ := by
  classical
  exact (Finset.univ.filter fun v ↦
    IsAuthenticationBoundary (subtree v) (sibling v) queries).card

/-- Uniform expectation of a natural-valued statistic on `t` independent samples. -/
def uniformQueryExpectation {alpha : Type*} [Fintype alpha] (t : ℕ)
    (statistic : (Fin t → alpha) → ℕ) : ℚ := by
  classical
  exact (∑ queries, (statistic queries : ℚ)) / (Fintype.card alpha : ℚ) ^ t

private def queriesAvoidEquiv {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {t : ℕ} (S : Finset alpha) :
    ({queries : Fin t → alpha // QueriesAvoid S queries}) ≃
      (Fin t → {x : alpha // x ∉ S}) := by
  classical
  exact
    { toFun := fun queries i ↦ ⟨queries.1 i, by simpa using queries.2 i⟩
      invFun := fun queries ↦ ⟨fun i ↦ queries i, fun i ↦ by simpa using (queries i).2⟩
      left_inv := fun queries ↦ by cases queries; rfl
      right_inv := fun queries ↦ by funext i; exact Subtype.ext rfl }

/-- Exactly `(n-|S|)^t` independent query tuples avoid a fixed subset `S`. -/
theorem card_queriesAvoid {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {t : ℕ} (S : Finset alpha) :
    (Finset.univ.filter fun queries : Fin t → alpha ↦ QueriesAvoid S queries).card =
      (Fintype.card alpha - S.card) ^ t := by
  classical
  let _ : Fintype {queries : Fin t → alpha // QueriesAvoid S queries} := Fintype.ofFinite _
  let _ : Fintype {x : alpha // x ∉ S} := Fintype.ofFinite _
  calc
    (Finset.univ.filter fun queries : Fin t → alpha ↦ QueriesAvoid S queries).card =
        Fintype.card {queries : Fin t → alpha // QueriesAvoid S queries} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card (Fin t → {x : alpha // x ∉ S}) :=
      Fintype.card_congr (queriesAvoidEquiv S)
    _ = (Fintype.card alpha - S.card) ^ t := by
      rw [Fintype.card_fun, Fintype.card_subtype]
      simp only [Fintype.card_fin]
      congr 1
      rw [← Finset.card_compl S]
      congr 1
      ext x
      simp

/-- The number of query tuples exposing one oriented boundary is the difference between avoiding
the subtree and avoiding the union of the subtree with its sibling. -/
theorem card_authenticationBoundary {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {t : ℕ} (subtree sibling : Finset alpha) :
    (Finset.univ.filter fun queries : Fin t → alpha ↦
      IsAuthenticationBoundary subtree sibling queries).card =
      (Fintype.card alpha - subtree.card) ^ t -
        (Fintype.card alpha - (subtree ∪ sibling).card) ^ t := by
  classical
  let avoidsSubtree := Finset.univ.filter fun queries : Fin t → alpha ↦
    QueriesAvoid subtree queries
  let avoidsUnion := Finset.univ.filter fun queries : Fin t → alpha ↦
    QueriesAvoid (subtree ∪ sibling) queries
  have hsubset : avoidsUnion ⊆ avoidsSubtree := by
    intro queries hqueries
    simp only [avoidsUnion, avoidsSubtree, Finset.mem_filter, Finset.mem_univ,
      true_and] at hqueries ⊢
    intro i hi
    exact hqueries i (Finset.mem_union_left _ hi)
  have hevent : (Finset.univ.filter fun queries : Fin t → alpha ↦
      IsAuthenticationBoundary subtree sibling queries) = avoidsSubtree \ avoidsUnion := by
    ext queries
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      avoidsSubtree, avoidsUnion]
    change (QueriesAvoid subtree queries ∧ ¬QueriesAvoid sibling queries) ↔
      QueriesAvoid subtree queries ∧ ¬QueriesAvoid (subtree ∪ sibling) queries
    constructor
    · rintro ⟨hS, hT⟩
      refine ⟨hS, fun hU ↦ hT ?_⟩
      intro i hi
      exact hU i (Finset.mem_union_right _ hi)
    · rintro ⟨hS, hU⟩
      refine ⟨hS, fun hT ↦ hU ?_⟩
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hS i hi
      · exact hT i hi
  rw [hevent, Finset.card_sdiff_of_subset hsubset, card_queriesAvoid,
    card_queriesAvoid]

/-- Exact expected authentication count for any finite family of oriented sibling boundaries. -/
theorem uniformQueryExpectation_authenticationHashCount
    {alpha node : Type*} [Fintype alpha] [Fintype node] [DecidableEq alpha]
    {t : ℕ} (subtree sibling : node → Finset alpha) :
    uniformQueryExpectation t (authenticationHashCount subtree sibling) =
      ∑ v, (((Fintype.card alpha - (subtree v).card) ^ t -
          (Fintype.card alpha - (subtree v ∪ sibling v).card) ^ t : ℕ) : ℚ) /
        (Fintype.card alpha : ℚ) ^ t := by
  classical
  unfold uniformQueryExpectation authenticationHashCount
  simp_rw [show ∀ queries : Fin t → alpha,
      ((Finset.univ.filter fun v ↦
        IsAuthenticationBoundary (subtree v) (sibling v) queries).card : ℚ) =
          ∑ v, if IsAuthenticationBoundary (subtree v) (sibling v) queries
            then (1 : ℚ) else 0 by
      intro queries
      exact (Finset.sum_boole _ _).symm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_boole, card_authenticationBoundary]
  rw [Finset.sum_div]

/-- If every subtree has size `s`, is disjoint from an equally sized sibling, and there are `b`
oriented nodes, the expected boundary count has the usual closed form. -/
theorem uniformQueryExpectation_authenticationHashCount_of_uniformSize
    {alpha node : Type*} [Fintype alpha] [Fintype node] [DecidableEq alpha]
    {t s b : ℕ} (subtree sibling : node → Finset alpha)
    (hnodes : Fintype.card node = b)
    (hsubtree : ∀ v, (subtree v).card = s)
    (hsibling : ∀ v, (sibling v).card = s)
    (hdisjoint : ∀ v, Disjoint (subtree v) (sibling v)) :
    uniformQueryExpectation t (authenticationHashCount subtree sibling) =
      (b : ℚ) * (((Fintype.card alpha - s) ^ t -
        (Fintype.card alpha - 2 * s) ^ t : ℕ) : ℚ) /
          (Fintype.card alpha : ℚ) ^ t := by
  classical
  rw [uniformQueryExpectation_authenticationHashCount subtree sibling]
  simp_rw [hsubtree]
  have hunion (v : node) : (subtree v ∪ sibling v).card = 2 * s := by
    rw [Finset.card_union_of_disjoint (hdisjoint v), hsubtree v, hsibling v]
    omega
  simp_rw [hunion]
  simp [hnodes]
  ring

/-- Probability form of the uniform-size identity.  This is the expression used level by level
in a binary tree: the first power is the probability that the subtree is empty, and the second
is the probability that both it and its sibling are empty. -/
theorem uniformQueryExpectation_authenticationHashCount_of_uniformSize_probability
    {alpha node : Type*} [Fintype alpha] [Fintype node] [DecidableEq alpha]
    {t s b : ℕ} (subtree sibling : node → Finset alpha)
    (hnonempty : 0 < Fintype.card alpha) (hnodes : Fintype.card node = b)
    (hsubtree : ∀ v, (subtree v).card = s)
    (hsibling : ∀ v, (sibling v).card = s)
    (hdisjoint : ∀ v, Disjoint (subtree v) (sibling v)) :
    uniformQueryExpectation t (authenticationHashCount subtree sibling) =
      (b : ℚ) * ((((Fintype.card alpha - s : ℕ) : ℚ) / Fintype.card alpha) ^ t -
        (((Fintype.card alpha - 2 * s : ℕ) : ℚ) / Fintype.card alpha) ^ t) := by
  rw [uniformQueryExpectation_authenticationHashCount_of_uniformSize subtree sibling
    hnodes hsubtree hsibling hdisjoint]
  rcases isEmpty_or_nonempty node with hnode | hnode
  · let _ : IsEmpty node := hnode
    have hb : b = 0 := by
      rw [← hnodes]
      exact Fintype.card_eq_zero
    subst b
    simp
  · have hunion (v : node) : (subtree v ∪ sibling v).card = 2 * s := by
      rw [Finset.card_union_of_disjoint (hdisjoint v), hsubtree v, hsibling v]
      omega
    have htwo : 2 * s ≤ Fintype.card alpha := by
      simpa [← hunion (Classical.choice hnode)] using
        Finset.card_le_univ (subtree (Classical.choice hnode) ∪
          sibling (Classical.choice hnode))
    have hpowers : (Fintype.card alpha - 2 * s) ^ t ≤
        (Fintype.card alpha - s) ^ t := Nat.pow_le_pow_left (by omega) t
    rw [Nat.cast_sub hpowers, Nat.cast_pow, Nat.cast_pow, div_pow, div_pow]
    have hcard : (Fintype.card alpha : ℚ) ≠ 0 := by positivity
    field_simp

end

end ArkLib.UniformQueryBoundary
