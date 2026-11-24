/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Fin

/-! # Sums over finite coordinate domains

This file splits dependent finite products into their first coordinate and tail.

It transports uniform product sums along equality of dimensions.

It counts tuples by their first coordinate.
-/

@[expose] public section

namespace Fin

/-- Split a dependent finite product into its first coordinate and remaining coordinates. -/
theorem sum_piFinset_cons {n : ℕ} {α : Fin (n + 1) → Type*}
    {M : Type*} [AddCommMonoid M] (S : ∀ i, Finset (α i)) (f : (∀ i, α i) → M) :
    ∑ x ∈ Fintype.piFinset S, f x =
      ∑ a ∈ S 0, ∑ y ∈ Fintype.piFinset (Fin.tail S), f (Fin.cons a y) := by
  classical
  rw [← Finset.sum_product']
  have h := Finset.filter_piFinset_eq_map_consEquiv (S := S) (fun _ => True)
  simp only [Finset.filter_true] at h
  rw [h, Finset.sum_map]
  rfl

/-- Reindex a uniform finite product along equality of its dimensions. -/
theorem sum_piFinset_cast {R M : Type*} [AddCommMonoid M] (S : Finset R)
    {k l : ℕ} (h : k = l) (f : (Fin k → R) → M) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin k => S), f x =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin l => S), f (x ∘ Fin.cast h) := by
  subst l
  rfl

/-- Count the tuples satisfying a predicate by splitting off their first coordinate. -/
theorem card_filter_cons {n : ℕ} {α : Type*} [Fintype α] (p : (Fin (n + 1) → α) → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ a : α, (Finset.univ.filter fun t : Fin n → α => p (Fin.cons a t)).card := by
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => α)
    (fun x => if p (Fin.cons x.1 x.2) then 1 else 0) _ (fun _ => rfl), Fintype.sum_prod_type]

end Fin
