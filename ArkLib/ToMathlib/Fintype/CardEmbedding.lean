/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-!
# Embeddings of `Fin n` counted by their images

An embedding `f : Fin n ↪ α` has the `n`-element image `univ.map f`, and an `n`-element set `S`
is the image of exactly `n!` embeddings, one for each bijection `Fin n ≃ S`. A property of
embeddings that depends only on the image therefore holds for `n!` times as many embeddings as
there are `n`-element sets with the property.

## Main statements

* `Fintype.card_filter_embedding_map_univ_eq_factorial`: an `n`-element set is the image of
  exactly `n!` embeddings `Fin n ↪ α`.
* `Fintype.card_filter_embedding_map_univ`: for `P : Finset α → Prop`,
  `#{f : Fin n ↪ α | P (univ.map f)} = n ! * #{S : {S : Finset α // #S = n} | P S}`.
-/

@[expose] public section

open Finset Nat

namespace Fintype

variable {α : Type*} [Fintype α]

/-- The embeddings `Fin n ↪ α` with image `S` correspond to the bijections `Fin n ≃ S`. -/
private noncomputable def embeddingMapUnivEquiv {n : ℕ} (S : Finset α) :
    {f : Fin n ↪ α // univ.map f = S} ≃ (Fin n ≃ S) where
  toFun f := Equiv.ofBijective
    (fun i ↦ ⟨f.1 i, (congrArg (f.1 i ∈ ·) f.2).mp (mem_map_of_mem _ (mem_univ i))⟩)
    ⟨fun _ _ h ↦ f.1.injective (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨i, -, hi⟩ := mem_map.mp ((congrArg (y.1 ∈ ·) f.2).mpr y.2)
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S)), by
    ext x
    simp only [mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Function.Embedding.subtype_apply]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (e i).2, fun hx ↦ ⟨e.symm ⟨x, hx⟩, by simp⟩⟩⟩
  left_inv _ := Subtype.ext (Function.Embedding.ext fun _ ↦ rfl)
  right_inv _ := Equiv.ext fun _ ↦ rfl

/-- An `n`-element set is the image of exactly `n!` embeddings `Fin n ↪ α`. -/
theorem card_filter_embedding_map_univ_eq_factorial [DecidableEq α] {n : ℕ} {S : Finset α}
    (hS : #S = n) :
    #{f : Fin n ↪ α | univ.map f = S} = n ! := by
  rw [← Fintype.card_subtype, Fintype.card_congr (embeddingMapUnivEquiv S),
    Fintype.card_equiv (S.equivFinOfCardEq hS).symm, Fintype.card_fin]

/-- A property of embeddings `Fin n ↪ α` that depends only on the image holds for `n!` times as
many embeddings as there are `n`-element sets with the property. -/
theorem card_filter_embedding_map_univ (n : ℕ) (P : Finset α → Prop) [DecidablePred P] :
    #{f : Fin n ↪ α | P (univ.map f)} = n ! * #{S : {S : Finset α // #S = n} | P S} := by
  classical
  rw [card_eq_sum_card_fiberwise (t := {S : {S : Finset α // #S = n} | P S})
      (f := fun f ↦ (⟨univ.map f, by simp⟩ : {S : Finset α // #S = n}))
      fun f hf ↦ by simpa using hf,
    sum_const_nat (m := n !) fun S hS ↦ ?_, mul_comm]
  rw [← card_filter_embedding_map_univ_eq_factorial S.2, filter_filter]
  refine congrArg Finset.card (filter_congr fun f _ ↦ ?_)
  rw [Subtype.ext_iff]
  exact ⟨And.right, fun h ↦ ⟨by rw [h]; exact (mem_filter.mp hS).2, h⟩⟩

end Fintype
