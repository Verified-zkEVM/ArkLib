/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

/-!
  This module provides tools for picking a 
  subset from a finset. I.e., obtain a subset
  of a given finite set of a certain cardinality.
-/

namespace Finset

section PickSubset

variable {α : Type*} [DecidableEq α]

/-- Returns a subset of `s` of cardinality `n`
  if `#s ≥ n`, otherwise returns `s`.
-/
noncomputable def pickSubset (s : Finset α) (n : ℕ) : Finset α :=
  match n with
  | .zero => ∅ 
  | .succ n => 
    let subset_n := pickSubset s n
    if h : (s \ subset_n).Nonempty 
    then {Classical.choose (Finset.Nonempty.exists_mem h)} ∪ subset_n
    else subset_n

/-- Picking zero elements yields an empty set. -/
@[simp]
lemma pick_subset_zero {s : Finset α} :
  pickSubset s 0 = ∅ := rfl

/-- Picking from an empty set always yields an empty set. -/
@[simp]
lemma pick_subset_empty {n : ℕ} :
  pickSubset (∅ : Finset α) n = ∅ := by 
  induction n with
  | zero => rfl
  | succ n ih => simp [pickSubset, ih]

/-- `pickSubset s n` is indeed a subset of `s`. -/
lemma pick_subset_subset {s : Finset α} {n : ℕ} :
  pickSubset s n ⊆ s := by
  induction n with
  | zero => simp
  | succ n ih => 
    by_cases h : (s \ s.pickSubset n).Nonempty 
      <;> try 
        (simp only [pickSubset, h, ↓reduceDIte, ih, singleton_union])
    rw [Finset.insert_subset_iff]
    have h_choose := Classical.choose_spec (Finset.Nonempty.exists_mem h)
    aesop

/-- The cardinality of picked subset is `min s.card n`. -/
@[simp]
lemma card_pick_subset {s : Finset α} {n : ℕ} :
  (pickSubset s n).card = min s.card n := by 
  induction n generalizing s with
  | zero => simp [Finset.pickSubset]
  | succ n ih =>
    simp_all only [pickSubset, singleton_union]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem]
      · have := Finset.eq_of_subset_of_card_le 
          (Finset.pick_subset_subset : s.pickSubset n ⊆ s)
        aesop 
          (add safe (by omega))
          (add simp [min_def])
      · exact Classical.choose_spec h |> fun h' ↦ by aesop
    · simp_all only [nonempty_iff_ne_empty, ne_eq, sdiff_eq_empty_iff_subset, Decidable.not_not]
      have := Finset.card_le_card h 
      aesop (add safe (by omega))

@[simp]
lemma card_pick_subset_le {s : Finset α} {n : ℕ} :
  (pickSubset s n).card ≤ n := by simp 

/-- Picking non-zero elements from a non-empty set is not empty. -/
@[simp]
lemma nonempty_pick_subset_of_nonempty_of_ne {s : Finset α} {n : ℕ}
  (h : s.Nonempty)
  (hn : n ≠ 0) :
  (pickSubset s n).Nonempty := by 
  have h_card : (pickSubset s n).card ≠ 0 := by
    aesop
  rw [Finset.nonempty_iff_ne_empty]
  grind

/-- If the target cardinality `n` exceeds or is equal to the cardinality
  of the set `s` then `pickSubset` returns the whole set `s`. -/
lemma pick_subset_eq_s_of_card_le_n {s : Finset α} {n : ℕ}
  (h : s.card ≤ n) :
  pickSubset s n = s := by
  rw [←Finset.eq_iff_card_le_of_subset pick_subset_subset]
  simp [h]

/-- If the picked subset does not meet the target cardinality requirement
  then we must have obtained the original set `s`. -/
lemma pick_subset_eq_of_card_pick_subset_lt {s : Finset α} {n : ℕ}
  (h : (s.pickSubset n).card < n) :
  pickSubset s n = s := by
  rw [←Finset.eq_iff_card_le_of_subset pick_subset_subset]
  aesop (add safe (by omega))
  
/-- `pickSubset` is of cardinality `n` if it is a proper subset of `s`. -/
lemma pick_subset_card_eq_of_ne {s : Finset α} {n : ℕ}
  (h : pickSubset s n ≠ s) :
  (pickSubset s n).card = n := by
  by_contra contra
  exact h ∘ pick_subset_eq_of_card_pick_subset_lt <| 
    lt_of_le_of_ne (by simp) contra 
  
end PickSubset

end Finset
