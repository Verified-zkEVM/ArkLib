/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Gregor Mitscha-Baude
-/

import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Lattice

/-!
# Auxiliary lemmas for `List`
-/

universe u v w

namespace List

theorem append_getLast_dropLast {α : Type u} (l : List α) (h : l ≠ []) :
  l.dropLast ++ [l.getLast h] = l := by
  induction l with
  | nil =>
    contradiction
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp [dropLast, getLast]
    | cons hd' tl' =>
      simp only [dropLast_cons₂, getLast]
      simp only [cons_append, cons.injEq, true_and]
      apply ih

theorem foldl_split_outer {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) (h : l ≠ []): foldl (f:=f) (init:=init) (l)
    = f (foldl (f:=f) (init:=init) (l.dropLast)) (l.getLast (by omega)) := by
  conv_lhs => rw [← append_getLast_dropLast l h]
  rw [foldl_append]
  rfl

theorem foldl_split_inner {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) (h : l ≠ []): foldl (f:=f) (init:=init) (l)
    = foldl (f:=f) (init:=f (init) (l.head (by omega))) (l.tail) := by
  have h_l_eq: l = cons (l.head (by omega)) (l.tail) := by
    exact Eq.symm (head_cons_tail l h)
  conv_lhs => enter [3]; rw [h_l_eq]
  rw [foldl_cons]

theorem foldr_split_outer {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (l : List α) (h : l ≠ []): foldr (f:=f) (init:=init) (l)
    = f (l.head (by omega)) (foldr (f:=f) (init:=init) (l.tail)) := by
  have h_l_eq: l = cons (l.head (by omega)) (l.tail) := by
    exact Eq.symm (head_cons_tail l h)
  conv_lhs => enter [3]; rw [h_l_eq]
  rw [foldr_cons]

theorem foldr_split_inner {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (l : List α) (h : l ≠ []): foldr (f:=f) (init:=init) (l)
    = foldr (f:=f) (init:=f (l.getLast (by omega)) (init)) (l.dropLast) := by
  conv_lhs => rw [← append_getLast_dropLast l h]
  rw [foldr_append]
  rfl

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)

theorem mapM_single (f : α → m β) (a : α) : List.mapM f [a] = return [← f a] := by
  rw [← List.mapM'_eq_mapM]
  simp only [mapM', bind_pure_comp, map_pure]

@[simp]
theorem getLastI_append_single [Inhabited α] (x : α) : (l ++ [x]).getLastI = x := by
  simp only [List.getLastI_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
    Option.some_or]

variable {α : Type*} {unit : α}

@[simp] theorem leftpad_eq_self (l : List α) (n : Nat) (h : l.length ≥ n) :
    leftpad n unit l = l := by simp [leftpad, Nat.sub_eq_zero_of_le h]

@[simp] theorem rightpad_length (n : Nat) (unit : α) (l : List α) :
    (rightpad n unit l).length = max n l.length := by
  simp only [rightpad, length_append, length_replicate, Nat.add_comm l.length _, Nat.sub_add_eq_max]

@[simp] theorem rightpad_prefix (n : Nat) (unit : α) (l : List α) :
    l <+: rightpad n unit l := by
  simp only [IsPrefix, rightpad]
  exact Exists.intro (replicate (n - l.length) unit) rfl

@[simp] theorem rightpad_suffix (n : Nat) (unit : α) (l : List α) :
    replicate (n - l.length) unit <:+ rightpad n unit l := by
  simp only [IsSuffix, rightpad]
  exact Exists.intro l rfl

@[simp] theorem rightpad_eq_self (l : List α) (n : Nat) (h : n ≤ l.length) :
    rightpad n unit l = l := by simp [rightpad, Nat.sub_eq_zero_of_le h]

theorem rightpad_eq_rightpad_max (l : List α) (n : Nat) :
    rightpad n unit l = rightpad (max n l.length) unit l := by simp [rightpad]; omega

theorem rightpad_eq_rightpad_append_replicate_of_ge
  (l : List α) (m n : Nat) (h : n ≤ m) :
    rightpad m unit l = rightpad n unit l ++ replicate (m - max n l.length) unit := by
  simp [rightpad]; omega

theorem rightpad_eq_if_rightpad_eq_of_ge (l l' : List α) (m n n' : Nat) (h : n ≤ m) (h' : n' ≤ m) :
    rightpad n unit l = rightpad n' unit l' →
        rightpad m unit l = rightpad m unit l' := by
  intro hEq
  rw [rightpad_eq_rightpad_append_replicate_of_ge l _ n h]
  rw [rightpad_eq_rightpad_append_replicate_of_ge l' _ n' h']
  have hLen : max n l.length = max n' l'.length := calc
    max n l.length = (rightpad n unit l).length := Eq.symm (rightpad_length n unit l)
    _ = (rightpad n' unit l').length := congrArg length hEq
    _ = max n' l'.length := rightpad_length n' unit l'
  simp [hLen]
  sorry

@[simp] theorem rightpad_twice_eq_rightpad_max (m n : Nat) (unit : α) (l : List α) :
    rightpad n unit (rightpad m unit l) = rightpad (max m n) unit l := by
  rw (config := { occs := .neg [0] }) [rightpad, rightpad_length]
  simp [rightpad]
  by_cases h : m.max n ≤ l.length
  · simp [Nat.max_le.mp h]
  · refine Nat.eq_sub_of_add_eq ?_
    conv => { enter [1, 1]; rw [Nat.add_comm] }
    rw [Nat.add_assoc, Nat.sub_add_eq_max, Nat.sub_add_eq_max]
    simp at h
    by_cases h' : m ≤ l.length <;> omega

-- lemma getD_eq_getElem {l : List α} {i : Nat} {unit : α} (hi : i < l.length) :
--     l.getD i unit = l[i] := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi, Option.getD_some]

-- lemma getD_eq_default {l : List α} {i : Nat} {unit : α} (hi : i ≥ l.length) :
--     l.getD i unit = unit := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_none hi, Option.getD_none]

@[simp] theorem rightpad_getD_eq_getD (l : List α) (n : Nat) (unit : α) (i : Nat) :
    (rightpad n unit l).getD i unit = l.getD i unit := by
  rcases (Nat.lt_or_ge i l.length) with h_lt | h_ge
  · have h_lt': i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    simp only [h_lt, h_lt', getD_eq_getElem] -- eliminate `getD`
    simp [h_lt]
  rw [getD_eq_default _ _ h_ge] -- eliminate second `getD` for `unit`
  rcases (Nat.lt_or_ge i n) with h_lt₂ | h_ge₂
  · have h_lt' : i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_getElem _ _ h_lt'] -- eliminate first `getD`
    simp [h_ge]
  · have h_ge' : i ≥ (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_default _ _ h_ge'] -- eliminate first `getD`

theorem rightpad_getElem_eq_getD {a b : List α} {unit : α} {i : Nat}
  (h : i < (a.rightpad b.length unit).length) :
    (a.rightpad b.length unit)[i] = a.getD i unit := by
  rw [← rightpad_getD_eq_getD a b.length, getD_eq_getElem _ _ h]

/-- Given two lists of potentially different lengths, right-pads the shorter list with `unit`
  elements until they are the same length. -/
def matchSize (l₁ : List α) (l₂ : List α) (unit : α) : List α × List α :=
  (l₁.rightpad (l₂.length) unit, l₂.rightpad (l₁.length) unit)

theorem matchSize_comm (l₁ : List α) (l₂ : List α) (unit : α) :
    matchSize l₁ l₂ unit = (matchSize l₂ l₁ unit).swap := by
  simp [matchSize]

/-- `List.matchSize` returns two equal lists iff the two lists agree at every index `i : Nat`
  (extended by `unit` if necessary). -/
theorem matchSize_eq_iff_forall_eq (l₁ l₂ : List α) (unit : α) :
    (fun (x, y) => x = y) (matchSize l₁ l₂ unit) ↔ ∀ i : Nat, l₁.getD i unit = l₂.getD i unit :=
  by sorry
    -- TODO: finish this lemma based on `rightpad_getD_eq_getD`

/-- `List.dropWhile` but starting from the last element. Performed by `dropWhile` on the reversed
  list, followed by a reversal. -/
def dropLastWhile (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

lemma zipWith_const {α β : Type _} {f : α → β → β} {l₁ : List α} {l₂ : List β}
  (h₁ : l₁.length = l₂.length) (h₂ : ∀ a b, f a b = b) : l₁.zipWith f l₂ = l₂ := by
  induction' l₁ with hd tl ih generalizing l₂ <;> rcases l₂ <;> aesop

end List
