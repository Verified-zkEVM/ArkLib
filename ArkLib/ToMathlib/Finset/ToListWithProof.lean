/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Dedup

namespace Finset

/-- A helper to convert a finset into
  a list whose elements are the members of the finset,
  i.e. come with a proof that they belong to the finset.
-/
noncomputable def toListWithProof.{u} {α : Type u} [DecidableEq α] (s : Finset α) :
  List s :=
  let list := s.toList
  List.reduceOption <|
    list.map (fun x ↦ if h : x ∈ s then some ⟨x, h⟩ else none)

@[simp]
lemma toListWithProof_empty.{u} {α : Type u} [DecidableEq α] :
  toListWithProof (∅ : Finset α) = [] := by
  simp [toListWithProof, List.reduceOption]

lemma toListWithProof_mem.{u} {α : Type u} [DecidableEq α]
  {x : α}
  {s : Finset α}
  (hx : x ∈ s) :
  ⟨x, hx⟩ ∈ toListWithProof s := by
  simp [toListWithProof, List.reduceOption, hx]

private lemma list_reduceOption_helper
  {α : Type*} [DecidableEq α] {s : Finset α}
  {l : List α} (h : ∀ x ∈ l, x ∈ s) :
    List.map Subtype.val
      (List.reduceOption (l.map (fun x ↦ if hx : x ∈ s then some ⟨x, hx⟩ else none)))
        = l := by
  induction l with
  | nil => simp [List.reduceOption]
  | cons a t ih =>
    have ha := h a (by simp)
    simp only [List.map_cons, ha, dite_true, List.reduceOption, List.filterMap_cons, id]
    change a :: List.map Subtype.val _ = a :: t
    congr 1
    exact ih (fun x hx ↦ h x (List.mem_cons_of_mem a hx))

@[simp]
lemma toListWithProof_eq_toList.{u} {α : Type u} [DecidableEq α]
  {s : Finset α} :
  (toListWithProof s).map (fun x ↦ x.1) =
    s.toList := by
  simp only [toListWithProof]
  exact list_reduceOption_helper (fun x hx ↦ Finset.mem_toList.mp hx)

end Finset

