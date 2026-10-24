/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Vector.Lookup
import Mathlib.Algebra.Field.ZMod

/-! Count budgets recover lookup inclusion and exact multiset equality. -/

namespace LookupCharacteristic.Test

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Duplicate table positions carry arbitrary field weights whose total at key zero is one.
example (i : Fin 2) : ∃ j : Fin 3,
    (#v[0, 0, 1] : Vector (Fin 2) 3)[j.val] = (#v[0, 1] : Vector (Fin 2) 2)[i.val] :=
  Vector.exists_getElem_eq_of_sumFiber_eq_count_of_length_lt_char (R := F) 5
    #v[0, 0, 1] #v[0, 1] (fun j ↦ (#v[-1, 2, 1] : Vector F 3)[j.val])
    (by decide) (by decide) i

-- Characteristic zero needs no public length budget.
example (i : Fin 8) : ∃ j : Fin 1,
    (#v[0] : Vector (Fin 2) 1)[j.val] = (#v[0, 0, 0, 0, 0, 0, 0, 0] : Vector (Fin 2) 8)[i.val] :=
  Vector.exists_getElem_eq_of_sumFiber_eq_count_of_charZero (R := ℤ)
    #v[0] #v[0, 0, 0, 0, 0, 0, 0, 0] (fun _ ↦ 8) (by decide) i

private theorem reordered_counts (k : String) :
    List.count k ["a", "b", "a"] = List.count k ["b", "a", "a"] := by
  simp [List.count_cons, Nat.add_comm, Nat.add_left_comm]

-- String has no finite carrier: the inference uses equality and finite occurrence counts only.
example : List.Perm ["a", "b", "a"] ["b", "a", "a"] :=
  List.perm_of_cast_count_eq (R := ℤ) _ _ Nat.cast_injective
    (fun k ↦ congrArg (Nat.cast : ℕ → ℤ) (reordered_counts k))

example : List.Perm ["a", "b", "a"] ["b", "a", "a"] :=
  List.perm_of_cast_count_eq_of_length_lt_char (R := F) 5 _ _ (by decide) (by decide)
    (fun k ↦ congrArg (Nat.cast : ℕ → F) (reordered_counts k))

example : (#v["a", "b", "a"] : Vector String 3).Perm #v["b", "a", "a"] :=
  Vector.perm_of_cast_count_eq (R := ℤ) _ _ Nat.cast_injective
    (fun k ↦ congrArg (Nat.cast : ℕ → ℤ) (reordered_counts k))

example : (#v["a", "b", "a"] : Vector String 3).Perm #v["b", "a", "a"] :=
  Vector.perm_of_cast_count_eq_of_length_lt_char (R := F) 5 _ _ (by decide)
    (fun k ↦ congrArg (Nat.cast : ℕ → F) (reordered_counts k))

abbrev F₂ := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- A missing query repeated exactly p times balances with zero table weights.
example : (∀ k : Fin 2, Finset.univ.sumFiber
    (fun j : Fin 1 ↦ (#v[1] : Vector (Fin 2) 1)[j.val]) (fun _ ↦ (0 : F₂)) k =
      ((#v[0, 0] : Vector (Fin 2) 2).toList.count k : F₂)) ∧
    ¬ ∃ j : Fin 1, (#v[1] : Vector (Fin 2) 1)[j.val] = 0 := by
  constructor <;> decide

-- Equal-size multisets can have equal field counts and different exact multiplicities at p.
example : (∀ k : Fin 2,
    ((#v[0, 0, 0, 0, 0] : Vector (Fin 2) 5).toList.count k : F) =
      ((#v[1, 1, 1, 1, 1] : Vector (Fin 2) 5).toList.count k : F)) ∧
    ¬ (#v[0, 0, 0, 0, 0] : Vector (Fin 2) 5).Perm #v[1, 1, 1, 1, 1] := by
  constructor
  · decide
  · intro h
    exact (show (#v[0, 0, 0, 0, 0] : Vector (Fin 2) 5).toList.count 0 ≠
      (#v[1, 1, 1, 1, 1] : Vector (Fin 2) 5).toList.count 0 by decide) (h.toList.count_eq 0)

-- Bounding only one list is insufficient: counts one and six coincide in characteristic five.
example : (∀ k : Fin 1, (List.count k [0] : F) =
    (List.count k [0, 0, 0, 0, 0, 0] : F)) ∧
    ¬ List.Perm ([0] : List (Fin 1)) [0, 0, 0, 0, 0, 0] := by
  constructor
  · decide
  · intro h
    exact (show ([0] : List (Fin 1)).length ≠ [0, 0, 0, 0, 0, 0].length by decide) h.length_eq

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``List.perm_of_cast_count_eq, ``List.perm_of_cast_count_eq_of_length_lt_char,
      ``Vector.exists_getElem_eq_of_sumFiber_eq_count_of_length_lt_char,
      ``Vector.exists_getElem_eq_of_sumFiber_eq_count_of_charZero,
      ``Vector.perm_of_cast_count_eq, ``Vector.perm_of_cast_count_eq_of_length_lt_char] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end LookupCharacteristic.Test
