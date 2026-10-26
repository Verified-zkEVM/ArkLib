/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Finset.SumFiber
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Fintype.Fin

/-!
# Histograms of finite indices

`Vector.histogram` counts each selected index in one pass through an index vector. The counts are
natural numbers, so the construction and its correctness do not depend on a field characteristic.
The key-fiber theorem handles repeated table values by adding the counts of every table position
with the selected key.
-/

@[expose] public section

namespace Vector

variable {n m : ℕ}

/-- Count how often each finite index occurs, by incrementing a vector of natural counts. -/
def histogram (indices : Vector (Fin n) m) : Vector ℕ n :=
  indices.foldl (fun counts i ↦ counts.set i.val (counts[i.val] + 1) i.isLt)
    (Vector.replicate n 0)

private theorem getElem_foldl_histogram (indices : List (Fin n)) (counts : Vector ℕ n)
    (j : Fin n) :
    (indices.foldl (fun counts i ↦ counts.set i.val (counts[i.val] + 1) i.isLt)
      counts)[j.val] = counts[j.val] + indices.count j := by
  induction indices generalizing counts with
  | nil => simp
  | cons i indices ih =>
    rw [List.foldl_cons, ih]
    by_cases hij : i = j
    · subst i
      simp [Nat.add_assoc, Nat.add_comm]
    · have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      simp [Vector.getElem_set_ne i.isLt j.isLt hval, List.count_cons_of_ne hij]

/-- Each output entry is the number of occurrences of its index. -/
@[simp]
theorem getElem_histogram (indices : Vector (Fin n) m) (j : Fin n) :
    (histogram indices)[j.val] = indices.toList.count j := by
  unfold histogram
  rw [← Vector.foldl_toList]
  simpa using getElem_foldl_histogram indices.toList (Vector.replicate n 0) j

private theorem sum_count_eq_countP {α : Type*} [Fintype α] [DecidableEq α]
    (indices : List α) (p : α → Prop) [DecidablePred p] :
    ∑ j ∈ Finset.univ.filter p, indices.count j = indices.countP p := by
  rw [← Finset.sum_filter_count_eq_countP p indices]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
  · intro j hjuniv hj
    have hnot : j ∉ indices := by
      intro hmem
      exact hj (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem,
        (Finset.mem_filter.mp hjuniv).2⟩)
    exact List.count_eq_zero_of_not_mem hnot

/-- Summing index counts over one table-key fiber counts exactly the queries with that key.
The lookup witness chooses a table position for every query; table values may repeat. -/
theorem sumFiber_histogram {κ : Type*} [DecidableEq κ] (table : Vector κ n)
    (queries : Vector κ m) (indices : Vector (Fin n) m)
    (hlookup : ∀ i : Fin m, table[(indices[i.val]).val] = queries[i.val]) (k : κ) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ (histogram indices)[j.val]) k = queries.toList.count k := by
  simp only [Finset.sumFiber, getElem_histogram]
  rw [sum_count_eq_countP]
  have hmap : indices.map (fun j ↦ table[j.val]) = queries := by
    apply Vector.ext
    intro i hi
    simpa using hlookup ⟨i, hi⟩
  rw [← hmap, Vector.toList_map, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro j _
  simp

/-- Casting natural index counts preserves the key-fiber law, in every characteristic. -/
theorem sumFiber_cast_histogram {κ R : Type*} [DecidableEq κ] [AddCommMonoidWithOne R]
    (table : Vector κ n) (queries : Vector κ m) (indices : Vector (Fin n) m)
    (hlookup : ∀ i : Fin m, table[(indices[i.val]).val] = queries[i.val]) (k : κ) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ ((histogram indices)[j.val] : R)) k = (queries.toList.count k : R) := by
  exact (Finset.sumFiber_map (Nat.castAddMonoidHom R) Finset.univ
    (fun j : Fin n ↦ table[j.val]) (fun j ↦ (histogram indices)[j.val]) k).trans
    (congrArg (Nat.castAddMonoidHom R) (sumFiber_histogram table queries indices hlookup k))

end Vector
