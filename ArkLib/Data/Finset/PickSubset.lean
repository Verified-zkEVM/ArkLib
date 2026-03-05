import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

namespace Finset

section PickSubset

variable {α : Type*} [DecidableEq α]

noncomputable def pickSubset (s : Finset α) (n : ℕ) : Finset α :=
  match n with
  | .zero => ∅ 
  | .succ n => 
    let subset_n := pickSubset s n
    if h : (s \ subset_n).Nonempty then
      {Classical.choose (Finset.Nonempty.exists_mem h)} ∪ subset_n
    else subset_n

@[simp]
lemma pick_subset_zero {s : Finset α} :
  pickSubset s 0 = ∅ := rfl

@[simp]
lemma pick_subset_emptyset {n : ℕ} :
  pickSubset (∅ : Finset α) n = ∅ := by 
  induction' n with n ih
  · rfl
  · simp [pickSubset, ih]

lemma pick_subset_subset {s : Finset α} {n : ℕ} :
  pickSubset s n ⊆ s := by
  induction' n with n ih
  · simp
  · simp [pickSubset]
    by_cases h : (s \ s.pickSubset n).Nonempty
    · simp [h] 
      rw [Finset.insert_subset_iff]
      simp [ih]
      have h_choose := Classical.choose_spec (Finset.Nonempty.exists_mem h)
      apply Finset.mem_of_subset
      · exact Finset.sdiff_subset (t := s.pickSubset n) 
      · exact h_choose 
    · simp [h, ih]

@[simp]
lemma card_pick_subset {s : Finset α} {n : ℕ} :
  (pickSubset s n).card = min s.card n := by 
  induction' n with n ih generalizing s <;> simp_all +decide [ Finset.pickSubset ];
  split_ifs with h;
  · rw [ Finset.card_insert_of_notMem ];
    · rw [ ih, min_def, min_def ] ; split_ifs <;> simp_all +arith +decide [ Finset.card_sdiff ] ;
      · have := Finset.eq_of_subset_of_card_le 
          ( Finset.pick_subset_subset : s.pickSubset n ⊆ s ) ; aesop;
      · omega
      · omega
    · exact Classical.choose_spec h |> fun h' => by aesop;
  · simp_all +decide [ Finset.nonempty_iff_ne_empty ];
    rw [ le_antisymm ( Finset.card_le_card h ) ];
    · grind +ring;
    · exact Finset.card_le_card ( Finset.pick_subset_subset )

lemma pick_subset_eq_s_of_card_le_n {s : Finset α} {n : ℕ}
  (h : s.card ≤ n)
  :
  pickSubset s n = s := by
  rw [←Finset.eq_iff_card_le_of_subset pick_subset_subset]
  simp [h]

lemma pick_subset_eq_s_of_card_pick_subset_lt_n {s : Finset α} {n : ℕ}
  (h : (s.pickSubset n).card < n)
  :
  pickSubset s n = s := by
  simp at h
  rw [←Finset.eq_iff_card_le_of_subset pick_subset_subset]
  simp 
  omega

end PickSubset

end Finset
