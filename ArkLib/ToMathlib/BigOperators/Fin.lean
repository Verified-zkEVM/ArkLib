/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma, Chung Thai Nguyen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# More lemmas about `Fin` and big operators
-/

@[expose] public section

namespace Fin

/-- The sums of `f` over the even and over the odd naturals below `2 * m` add up to its sum
over `Fin (m * 2)`. This is the finite analogue of `tsum_even_add_odd`. -/
theorem sum_even_add_odd {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ x : Fin m, f (2 * x) + ∑ x : Fin m, f (2 * x + 1) = ∑ x : Fin (m * 2), f x := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Fin.sum_univ_two, finProdFinEquiv, mul_comm, add_comm]

open Finset in
/-- A union bound for a tuple of challenges sampled one after the other.

A tuple `c` of `r + 1` challenges in `α` is bad when its first entry satisfies `p`, or when
its tail satisfies `Q` for that first entry.
The bad tuples number at most `#{a | p a} · |α|^r + ∑ a, #{c' | Q a c'}`.
The predicate `Q a` may depend on the first entry, which models a later round whose state
depends on the earlier challenges. -/
theorem card_filter_or_tail_le {α : Type*} [Fintype α] {r : ℕ} (p : α → Prop)
    [DecidablePred p] (Q : α → (Fin r → α) → Prop) [∀ a, DecidablePred (Q a)] :
    #{c : Fin (r + 1) → α | p (c 0) ∨ Q (c 0) (Fin.tail c)} ≤
      #{a | p a} * Fintype.card α ^ r + ∑ a, #{c : Fin r → α | Q a c} := by
  classical
  have hequiv : #{c : Fin (r + 1) → α | p (c 0) ∨ Q (c 0) (Fin.tail c)} =
      #{x : α × (Fin r → α) | p x.1 ∨ Q x.1 x.2} :=
    Finset.card_equiv (Fin.consEquiv fun _ ↦ α).symm (by simp)
  have hp : #{x : α × (Fin r → α) | p x.1} = #{a | p a} * Fintype.card α ^ r := by
    rw [show ({x : α × (Fin r → α) | p x.1} : Finset _) = ({a | p a} : Finset α) ×ˢ univ by
        ext; simp,
      card_product, card_univ, Fintype.card_fun, Fintype.card_fin]
  have hQ : #{x : α × (Fin r → α) | Q x.1 x.2} = ∑ a, #{c : Fin r → α | Q a c} := by
    rw [card_filter, Fintype.sum_prod_type]
    simp only [card_filter]
  rw [hequiv, filter_or, ← hp, ← hQ]
  exact card_union_le _ _

end Fin
