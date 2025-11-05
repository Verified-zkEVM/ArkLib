/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Finset.Image

/-!
  # Definitions and lemmas related to `Finset`.
-/

def erase_odd (s : Finset ℕ) : Finset ℕ := s.filter Even
def erase_even (s : Finset ℕ) : Finset ℕ := s.filter Odd

@[simp]
lemma erase_odd_empty :
    erase_odd ∅ = ∅ := rfl

lemma erase_odd_def {s : Finset ℕ} :
    erase_odd s = s.filter Even := rfl

@[simp]
lemma erase_even_empty :
    erase_even ∅ = ∅ := rfl

lemma erase_even_def {s : Finset ℕ} :
    erase_even s = s.filter Odd := rfl

def shift_left (s : Finset ℕ) : Finset ℕ :=
  s.filterMap
    (fun n => match n with
      | 0 => .none
      | n + 1 => .some n
      )
    (by aesop)

@[simp]
lemma shift_left_empty :
    shift_left ∅ = ∅ := rfl

lemma shift_left_def {s : Finset ℕ} :
    shift_left s = s.filterMap
    (fun n => match n with
      | 0 => .none
      | n + 1 => .some n
      )
    (by aesop)
 := rfl

def mul_by_2 (s : Finset ℕ) : Finset ℕ :=
  s.map ⟨fun n => 2 * n, by {
    intro a b
    simp
  }⟩

@[simp]
lemma mul_by_empty :
    mul_by_2 ∅ = ∅ := rfl

lemma mul_by_2_def {s : Finset ℕ} :
    mul_by_2 s = s.map ⟨fun n => 2 * n, by {
      intro a b
      simp
    }⟩  := rfl

def divide_by_2 (s : Finset ℕ) : Finset ℕ :=
  (erase_odd s).image (fun n => n / 2)

@[simp]
lemma divide_by_2_empty :
    divide_by_2 ∅ = ∅ := rfl

lemma divide_by_2_def {s : Finset ℕ} :
    divide_by_2 s = (erase_odd s).image (fun n => n / 2) := rfl

@[simp]
theorem erase_odd_mem
  {s : Finset ℕ}
  {n : ℕ}
  : n ∈ (erase_odd s) ↔ Even n ∧ n ∈ s := by aesop (add simp erase_odd)

@[simp]
theorem erase_even_mem
  {s : Finset ℕ}
  {n : ℕ}
  : n ∈ (erase_even s) ↔ Odd n ∧ n ∈ s := by aesop (add simp erase_even)

@[simp]
theorem mul_by_2_mem {s : Finset ℕ} {d : ℕ} :
    d ∈ mul_by_2 s ↔ Even d ∧ (d / 2) ∈ s := by
  aesop (add simp [mul_by_2, Nat.even_iff], safe (by omega))

@[simp]
theorem divide_by_2_mem {s : Finset ℕ} {d : ℕ} :
  d ∈ divide_by_2 s ↔ 2 * d ∈ s := by
  simp only [divide_by_2, Finset.mem_image, erase_odd_mem]
  exact ⟨
    fun _ ↦ by aesop (add simp [Nat.even_iff, Nat.mul_div_cancel', Nat.dvd_iff_mod_eq_zero]),
    fun _ ↦ ⟨2 * d, by aesop⟩
  ⟩

@[simp]
theorem shift_left_mem {s : Finset ℕ} {d : ℕ} : d ∈ shift_left s ↔ (d + 1) ∈ s := by
  aesop (add simp shift_left) (add safe (by existsi d + 1))

@[simp]
def finRangeTo {k : ℕ} (i : ℕ) : Finset (Fin k) :=
  (List.take i (List.finRange k)).toFinset
