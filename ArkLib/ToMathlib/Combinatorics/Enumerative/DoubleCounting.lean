/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Double counting after deleting part of the right-hand side

Let `r : α → β → Prop` be a relation between finite sets `s : Finset α` and `t : Finset β`, and
suppose every `a ∈ s` is related to at least `A` elements of `t`. Delete a set `u` of elements of
`β`. Each `a ∈ s` loses at most `#u` of its incidences, so it keeps at least `A - #u` incidences in
`t \ u`. Summing over `s` and double counting gives

  `#s * (A - #u) ≤ ∑ b ∈ t \ u, #{a ∈ s | r a b}`.

In the agreement arguments that use this bound, `s` is a set of candidate points, `t` is a set of
positions (cuts), `r a b` says that `a` agrees with the data at position `b`, and `u` is the set of
positions that must be discarded (for example cuts that vanish identically).

## Main statements

* `Finset.card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff` — deleting `u` removes at most
  `#u` incidences of a single element.
* `Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff` — the sharp deletion estimate above.
* `Finset.card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff` — the weaker form
  `#s * (A - k + 1) ≤ …` under `#u < k` and `k ≤ A`.
* `Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow` and
  `Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow` — the same two bounds with
  `t = univ` in a finite type, summing over `uᶜ`.

## Proof outline

For a single `a`, `{b ∈ t | r a b} \ u = {b ∈ t \ u | r a b}`, and Mathlib's `Finset.le_card_sdiff`
bounds the left side below by `#{b ∈ t | r a b} - #u`. Summing over `a ∈ s` and applying
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` converts the sum over `s` into a sum of
fibre sizes over `t \ u`. The `A - k + 1` form follows from the sharp form by monotonicity of
truncated subtraction.
-/

@[expose] public section

namespace Finset

variable {α β : Type*} (r : α → β → Prop)

/-- Deleting a finite set `u` from `t` removes at most `#u` of the elements of `t` related to
`a`: `#{b ∈ t | r a b} - #u ≤ #{b ∈ t \ u | r a b}`. No relation between `u` and `t` is assumed;
elements of `u` outside `t`, or not related to `a`, only make the bound weaker. -/
theorem card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff [DecidableEq β]
    (t u : Finset β) (a : α) [DecidablePred (r a)] :
    #(t.bipartiteAbove r a) - #u ≤ #((t \ u).bipartiteAbove r a) := by
  have h : (t \ u).bipartiteAbove r a = t.bipartiteAbove r a \ u := by
    ext b
    simp only [mem_bipartiteAbove, mem_sdiff]
    tauto
  rw [h]
  exact le_card_sdiff u _

/-- **Double counting after deletion.** If every `a ∈ s` is related to at least `A` elements of
`t`, then after deleting any finite set `u` the fibres over `t \ u` still carry at least
`#s * (A - #u)` incidences:

  `#s * (A - #u) ≤ ∑ b ∈ t \ u, #{a ∈ s | r a b}`.

No hypothesis relates `A` to `#u`. When `#u ≥ A` the left side is `0` because subtraction on `ℕ`
is truncated, and the statement holds trivially. The set `u` need not be contained in `t`. -/
theorem card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff [DecidableEq β]
    [∀ a b, Decidable (r a b)] {s : Finset α} {t : Finset β} (u : Finset β) {A : ℕ}
    (hA : ∀ a ∈ s, A ≤ #(t.bipartiteAbove r a)) :
    #s * (A - #u) ≤ ∑ b ∈ t \ u, #(s.bipartiteBelow r b) := by
  calc
    #s * (A - #u) = ∑ _a ∈ s, (A - #u) := (sum_const_nat fun _ _ ↦ rfl).symm
    _ ≤ ∑ a ∈ s, #((t \ u).bipartiteAbove r a) := by
      refine sum_le_sum fun a ha ↦ ?_
      exact (Nat.sub_le_sub_right (hA a ha) _).trans
        (card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff r t u a)
    _ = ∑ b ∈ t \ u, #(s.bipartiteBelow r b) :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r

/-- **Double counting after deleting fewer than `k` elements.** If every `a ∈ s` is related to at
least `A` elements of `t`, `#u < k` and `k ≤ A`, then

  `#s * (A - k + 1) ≤ ∑ b ∈ t \ u, #{a ∈ s | r a b}`.

This follows from `card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff`, since `#u ≤ k - 1`.

The hypothesis `k ≤ A` is needed because `A - k + 1` is at least `1` for every `k > A`, while no
incidences need survive. For `A = 0`, `k = 1`, `u = ∅` and the empty relation, the right side is
`0` and the left side is `#s`. -/
theorem card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff [DecidableEq β]
    [∀ a b, Decidable (r a b)] {s : Finset α} {t : Finset β} (u : Finset β) {A k : ℕ}
    (hkA : k ≤ A) (hu : #u < k) (hA : ∀ a ∈ s, A ≤ #(t.bipartiteAbove r a)) :
    #s * (A - k + 1) ≤ ∑ b ∈ t \ u, #(s.bipartiteBelow r b) :=
  (Nat.mul_le_mul_left _ (by omega)).trans
    (card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff r u hA)

/-- `card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff` for `t = univ` in a finite type: if every
`a ∈ s` is related to at least `A` elements of `β`, then for every `u : Finset β`

  `#s * (A - #u) ≤ ∑ b ∈ uᶜ, #{a ∈ s | r a b}`. -/
theorem card_mul_sub_card_le_sum_compl_card_bipartiteBelow [Fintype β] [DecidableEq β]
    [∀ a b, Decidable (r a b)] {s : Finset α} (u : Finset β) {A : ℕ}
    (hA : ∀ a ∈ s, A ≤ #((univ : Finset β).bipartiteAbove r a)) :
    #s * (A - #u) ≤ ∑ b ∈ uᶜ, #(s.bipartiteBelow r b) := by
  simpa only [compl_eq_univ_sdiff] using
    card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff r u hA

/-- `card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff` for `t = univ` in a finite type: if
every `a ∈ s` is related to at least `A` elements of `β`, `#u < k` and `k ≤ A`, then

  `#s * (A - k + 1) ≤ ∑ b ∈ uᶜ, #{a ∈ s | r a b}`.

The hypothesis `k ≤ A` is needed for the reason given at
`card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff`. -/
theorem card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow [Fintype β] [DecidableEq β]
    [∀ a b, Decidable (r a b)] {s : Finset α} (u : Finset β) {A k : ℕ}
    (hkA : k ≤ A) (hu : #u < k)
    (hA : ∀ a ∈ s, A ≤ #((univ : Finset β).bipartiteAbove r a)) :
    #s * (A - k + 1) ≤ ∑ b ∈ uᶜ, #(s.bipartiteBelow r b) := by
  simpa only [compl_eq_univ_sdiff] using
    card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff r u hkA hu hA

end Finset
