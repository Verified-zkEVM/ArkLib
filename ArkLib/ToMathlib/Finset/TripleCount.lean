/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# Counting triples through their first coordinate

Let `α` be a finite type with `q` elements.
A predicate on triples `α × α × α` is counted one value of the first coordinate at a time.
If each value allows at most `q² E` pairs, then at most `q³ E` triples hold.

A second count adds a set `B` of first coordinates that is not bounded this way.
Every triple in `B × α × α` may hold, so it adds `#B · q²`.

## Main statements

* `Finset.card_filter_triples_le_mul`: a uniform count of pairs bounds the count of triples.
* `Finset.card_filter_triples_le_of_imp_or`: the same, outside a set of first coordinates.
-/

@[expose] public section

namespace Finset

open scoped Finset

variable {α : Type*} [Fintype α]

/-- A uniform count on the last two coordinates bounds the count of triples.

Here `q` is the size of `α`.
If every first coordinate allows at most `q² E` pairs, then at most `q³ E` triples hold. -/
theorem card_filter_triples_le_mul (p : α × α × α → Prop) [DecidablePred p] (E : ℝ)
    (h : ∀ θ, (#{x : α × α | p (θ, x.1, x.2)} : ℝ) ≤ (Fintype.card α : ℝ) ^ 2 * E) :
    (#{c : α × α × α | p c} : ℝ) ≤ (Fintype.card α : ℝ) ^ 3 * E := by
  have hsum : #{c : α × α × α | p c} = ∑ θ : α, #{x : α × α | p (θ, x.1, x.2)} := by
    rw [card_filter, Fintype.sum_prod_type]
    simp only [card_filter]
  rw [hsum, Nat.cast_sum]
  calc (∑ θ : α, (#{x : α × α | p (θ, x.1, x.2)} : ℝ))
      ≤ ∑ _θ : α, (Fintype.card α : ℝ) ^ 2 * E := sum_le_sum fun θ _ ↦ h θ
    _ = _ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring

/-- A uniform count on the last two coordinates, outside a set `B` of first coordinates.

Here `q` is the size of `α`.
Every triple satisfying `p` satisfies `a` or has its first coordinate in `B`.
If every first coordinate allows at most `q² E` pairs satisfying `a`,
then at most `q³ E + #B q²` triples satisfy `p`. -/
theorem card_filter_triples_le_of_imp_or {p a : α × α × α → Prop} [DecidablePred p]
    [DecidablePred a] (B : Finset α) {E : ℝ} (hp : ∀ c, p c → a c ∨ c.1 ∈ B)
    (ha : ∀ θ, (#{x : α × α | a (θ, x.1, x.2)} : ℝ) ≤ (Fintype.card α : ℝ) ^ 2 * E) :
    (#{c : α × α × α | p c} : ℝ) ≤
      (Fintype.card α : ℝ) ^ 3 * E + #B * (Fintype.card α : ℝ) ^ 2 := by
  classical
  have hsub : ({c | p c} : Finset (α × α × α)) ⊆ ({c | a c} : Finset _) ∪ B ×ˢ univ :=
    fun c hc ↦ by
      rcases hp c (mem_filter.mp hc).2 with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)
      · exact mem_union_right _ (mem_product.mpr ⟨h, mem_univ _⟩)
  have hB : (#(B ×ˢ (univ : Finset (α × α))) : ℝ) = #B * (Fintype.card α : ℝ) ^ 2 := by
    rw [card_product, card_univ, Fintype.card_prod]
    push_cast
    ring
  calc (#{c : α × α × α | p c} : ℝ) ≤ #(({c | a c} : Finset _) ∪ B ×ˢ univ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ #({c | a c} : Finset (α × α × α)) + #(B ×ˢ (univ : Finset (α × α))) := by
        exact_mod_cast card_union_le _ _
    _ ≤ _ := by
        rw [hB]
        gcongr
        exact card_filter_triples_le_mul a E ha

end Finset
