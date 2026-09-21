/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Acceptance tests for double counting after deletion

The examples check that the sharp deletion bound is attained on a concrete relation, that the
source statements at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` follow from the
generalized ones in their original `Fin n` form, and that the hypothesis `k ≤ A` of the
`A - k + 1` form cannot be dropped.
-/

namespace Finset

/-- The sharp bound is an equality for the full relation between `Fin 3` and `Fin 5` with two
deleted columns: each of the `3` rows keeps exactly `5 - 2` incidences, so both sides equal `9`. -/
example :
    let r : Fin 3 → Fin 5 → Prop := fun _ _ ↦ True
    let u : Finset (Fin 5) := {0, 1}
    #(univ : Finset (Fin 3)) * (5 - #u) =
        ∑ b ∈ uᶜ, #((univ : Finset (Fin 3)).bipartiteBelow r b) ∧
      #(univ : Finset (Fin 3)) * (5 - #u) ≤
        ∑ b ∈ uᶜ, #((univ : Finset (Fin 3)).bipartiteBelow r b) := by
  intro r u
  refine ⟨by decide, ?_⟩
  exact card_mul_sub_card_le_sum_compl_card_bipartiteBelow r u (A := 5) fun a _ ↦ by decide +revert

/-- The deleted set may lie outside `t`, and `#u` may exceed `A`. With `r a b ↔ a = b` on `ℕ`,
`s = t = {0, 1, 2}`, `A = 1` and `u = {5, 6}`, the left side is `3 * (1 - 2) = 0`. -/
example :
    #({0, 1, 2} : Finset ℕ) * (1 - #({5, 6} : Finset ℕ)) ≤
      ∑ b ∈ ({0, 1, 2} : Finset ℕ) \ {5, 6},
        #(({0, 1, 2} : Finset ℕ).bipartiteBelow (fun a b : ℕ ↦ a = b) b) :=
  card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff _ _ fun a ha ↦ by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> decide

/-- The per-element deletion estimate on a concrete relation: `a = 0` is related to the even
elements `{0, 2, 4}` of `t = range 6`; deleting `u = {2, 3}` removes one of them. -/
example :
    #((range 6).bipartiteAbove (fun (_ : ℕ) b ↦ b % 2 = 0) 0) - #({2, 3} : Finset ℕ) ≤
      #(((range 6) \ {2, 3}).bipartiteAbove (fun (_ : ℕ) b ↦ b % 2 = 0) 0) :=
  card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff _ _ _ _

/-- The source statement `AffineHilbert.finiteAgreementIncidence_lower_sharp`, in its `Fin n`
form with sums over `univ.filter (· ∉ Bad)`, follows from the generalized theorem. -/
example {X : Type*} {n A : ℕ} (S : Finset X) (Bad : Finset (Fin n)) (zero : X → Fin n → Prop)
    [∀ x i, Decidable (zero x i)]
    (hA : ∀ x ∈ S, A ≤ (univ.filter (zero x)).card) :
    S.card * (A - Bad.card) ≤
      ∑ i ∈ univ.filter (fun i ↦ i ∉ Bad), (S.filter fun x ↦ zero x i).card := by
  rw [filter_notMem_eq_sdiff]
  exact card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff zero Bad hA

/-- The source statement `AffineHilbert.finiteAgreementIncidence_lower`, in its `Fin n` form,
follows from the generalized `A - k + 1` theorem. -/
example {X : Type*} {n A k : ℕ} (S : Finset X) (Bad : Finset (Fin n)) (zero : X → Fin n → Prop)
    [∀ x i, Decidable (zero x i)] (hkA : k ≤ A) (hBad : Bad.card < k)
    (hA : ∀ x ∈ S, A ≤ (univ.filter (zero x)).card) :
    S.card * (A - k + 1) ≤
      ∑ i ∈ univ.filter (fun i ↦ i ∉ Bad), (S.filter fun x ↦ zero x i).card := by
  rw [filter_notMem_eq_sdiff]
  exact card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff zero Bad hkA hBad hA

/-- The hypothesis `k ≤ A` cannot be dropped from
`card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow`. With `A = 0`, `k = 1`, `u = ∅` and the
empty relation on `Fin 1`, the other hypotheses hold but the conclusion `1 * (0 - 1 + 1) ≤ 0`
is false. -/
example :
    ¬ ∀ (A k : ℕ) (u : Finset (Fin 1)), #u < k →
        (∀ a ∈ (univ : Finset (Fin 1)),
          A ≤ #((univ : Finset (Fin 1)).bipartiteAbove (fun _ _ ↦ False) a)) →
        #(univ : Finset (Fin 1)) * (A - k + 1) ≤
          ∑ b ∈ uᶜ, #((univ : Finset (Fin 1)).bipartiteBelow (fun _ _ ↦ False) b) := by
  intro h
  have := h 0 1 ∅ (by decide) (fun _ _ ↦ Nat.zero_le _)
  revert this
  decide

end Finset
