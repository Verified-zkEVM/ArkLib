/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Tactic.FinCases

/-! # Evaluation domains and wire labels for Plonk

An evaluation domain is any indexed family of distinct field points. Primitive roots give the
multiplicative subgroup instance. Three disjoint scaled copies supply the wire-position labels.
-/

@[expose] public section

namespace Plonk

/-- The `n` distinct nodes at which the columns of a Plonk circuit are evaluated. -/
structure EvaluationDomain (F : Type) [Field F] (n : ℕ) where
  /-- The node corresponding to each row. -/
  node : Fin n → F
  /-- Different rows have different nodes. -/
  injective : Function.Injective node

namespace EvaluationDomain

variable {F : Type} [Field F] {n : ℕ}

/-- The set of evaluation nodes. -/
def nodes (D : EvaluationDomain F n) : Set F := Set.range D.node

/-- Scaling the node set by `k`; for a multiplicative subgroup this is the coset `kH`. -/
def scaledNodes (D : EvaluationDomain F n) (k : F) : Set F :=
  Set.range (fun i => k * D.node i)

/-- Powers of a primitive root form an evaluation domain. -/
def primitiveRoot (ω : F) (hω : IsPrimitiveRoot ω n) : EvaluationDomain F n where
  node i := ω ^ (i : ℕ)
  injective i j hij := Fin.ext (hω.pow_inj i.isLt j.isLt hij)

@[simp]
theorem primitiveRoot_node (ω : F) (hω : IsPrimitiveRoot ω n) (i : Fin n) :
    (primitiveRoot ω hω).node i = ω ^ (i : ℕ) := rfl

/-- For positive order, the nodes are exactly the solutions to `x ^ n = 1`. -/
theorem primitiveRoot_nodes (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n) :
    (primitiveRoot ω hω).nodes = {x | x ^ n = 1} := by
  let : NeZero n := ⟨hn.ne'⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change (ω ^ (i : ℕ)) ^ n = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, hix⟩ := hω.eq_pow_of_pow_eq_one hx
    exact ⟨⟨i, hi⟩, hix⟩

/-- The subgroup of roots of unity, viewed in the field, is the primitive-root node set. -/
theorem primitiveRoot_nodes_eq_rootsOfUnity (ω : F) (hω : IsPrimitiveRoot ω n)
    (hn : 0 < n) :
    (primitiveRoot ω hω).nodes =
      ((↑) : Fˣ → F) '' (rootsOfUnity n F : Set Fˣ) := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [Units.val_set_image_rootsOfUnity, primitiveRoot_nodes ω hω hn]

end EvaluationDomain

/-- Nonzero multipliers whose three node sets `H`, `k₁H`, and `k₂H` are disjoint. -/
structure CosetLabels {F : Type} [Field F] {n : ℕ} (D : EvaluationDomain F n) where
  /-- Multiplier for the right-wire labels. -/
  k₁ : F
  /-- Multiplier for the output-wire labels. -/
  k₂ : F
  /-- The right-wire multiplier is nonzero. -/
  k₁_ne_zero : k₁ ≠ 0
  /-- The output-wire multiplier is nonzero. -/
  k₂_ne_zero : k₂ ≠ 0
  /-- Left and right labels lie in disjoint cosets. -/
  disjoint_left_right : Disjoint (D.scaledNodes 1) (D.scaledNodes k₁)
  /-- Left and output labels lie in disjoint cosets. -/
  disjoint_left_output : Disjoint (D.scaledNodes 1) (D.scaledNodes k₂)
  /-- Right and output labels lie in disjoint cosets. -/
  disjoint_right_output : Disjoint (D.scaledNodes k₁) (D.scaledNodes k₂)

namespace CosetLabels

variable {F : Type} [Field F] {n : ℕ} {D : EvaluationDomain F n}

/-- The multiplier `1`, `k₁`, or `k₂` of a wire column. -/
def multiplier (L : CosetLabels D) (c : Fin 3) : F :=
  if c = 0 then 1 else if c = 1 then L.k₁ else L.k₂

/-- The label of a row in a given wire column. -/
def columnLabel (L : CosetLabels D) (c : Fin 3) (i : Fin n) : F :=
  L.multiplier c * D.node i

/-- The label of a wire position in column-major order. -/
def label (L : CosetLabels D) (p : Fin (3 * n)) : F :=
  let ci := finProdFinEquiv.symm p
  L.columnLabel ci.1 ci.2

@[simp]
theorem label_column (L : CosetLabels D) (c : Fin 3) (i : Fin n) :
    L.label (finProdFinEquiv (c, i)) = L.columnLabel c i := by
  simp [label]

/-- Every column multiplier is nonzero. -/
theorem multiplier_ne_zero (L : CosetLabels D) (c : Fin 3) : L.multiplier c ≠ 0 := by
  fin_cases c <;> simp [multiplier, L.k₁_ne_zero, L.k₂_ne_zero]

/-- Each column has distinct labels. -/
theorem columnLabel_injective (L : CosetLabels D) (c : Fin 3) :
    Function.Injective (L.columnLabel c) := by
  intro i j hij
  exact D.injective ((mul_left_cancel₀ (L.multiplier_ne_zero c)) hij)

/-- The three columns have pairwise disjoint label sets. -/
theorem columnLabel_disjoint (L : CosetLabels D) {c d : Fin 3} (hcd : c ≠ d) :
    Disjoint (Set.range (L.columnLabel c)) (Set.range (L.columnLabel d)) := by
  fin_cases c <;> fin_cases d
  all_goals simp only [ne_eq, not_true_eq_false] at hcd
  · exact L.disjoint_left_right
  · exact L.disjoint_left_output
  · exact L.disjoint_left_right.symm
  · exact L.disjoint_right_output
  · exact L.disjoint_left_output.symm
  · exact L.disjoint_right_output.symm

/-- Coset disjointness gives distinct labels for all `3n` positions. -/
theorem label_injective (L : CosetLabels D) : Function.Injective L.label := by
  intro p q hpq
  obtain ⟨⟨c, i⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨d, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [label_column] at hpq
  have hcd : c = d := by
    by_contra hcd
    exact Set.disjoint_range_iff.mp (L.columnLabel_disjoint hcd) i j hpq
  subst d
  exact congrArg (fun i => finProdFinEquiv (c, i)) (L.columnLabel_injective c hpq)

end CosetLabels

end Plonk
