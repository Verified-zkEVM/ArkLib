/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Vector.Lookup
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Normalized lookup multiplicities and indexed histograms

Dividing each queried key count by its table count gives the same per-key aggregate as the
cast indexed histogram, provided the occurring table counts remain nonzero in the coefficient
field. The two vectors of weights can differ when table values repeat. The indexed histogram
itself needs no such division premise and works in every characteristic.

The normalization formula is an executable comparison view, separate from the honest runtime
histogram path. Keys need only explicit equality, not a finite ambient type. A numeric table
length below the characteristic suffices for nonzero normalizers; a query-length budget alone
need not imply this table-length condition, including when there are no queries.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22], Eq. (14) of the
  inspected March 31, 2023 author copy; source-version metadata is in `docs/kb/papers/Hab22.md`.
-/

@[expose] public section

open scoped BigOperators
namespace Vector
variable {κ F : Type*} [DecidableEq κ] [Field F] {n m : ℕ}

/-- Query counts divided by table counts, computed for comparison with indexed histograms.
Repeated table values receive the same weight; zero denominators use total field division. -/
def normalizedLookupWeights (F : Type*) [Field F] (table : Vector κ n)
    (queries : Vector κ m) : Vector F n :=
  table.map fun k ↦ (queries.toList.count k : F) / (table.toList.count k : F)

/-- Every normalized entry is the query count divided by the count of its table key. -/
@[simp] theorem getElem_normalizedLookupWeights (table : Vector κ n) (queries : Vector κ m)
    (j : Fin n) :
    (normalizedLookupWeights F table queries)[j.val] =
      (queries.toList.count table[j.val] : F) / (table.toList.count table[j.val] : F) := by
  simp [normalizedLookupWeights]

private theorem sum_ite_eq_count_mul (xs : List κ) (k : κ) (w : F) :
    (xs.map (fun x ↦ if x = k then w else 0)).sum = (xs.count k : F) * w := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = k
    · simp [h, ih, add_mul, _root_.add_comm]
    · simp [h, ih]

private theorem sumFiber_const_eq_count_mul (table : Vector κ n) (k : κ) (w : F) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val]) (fun _ ↦ w) k =
      (table.toList.count k : F) * w := by
  rw [Finset.sumFiber_eq_sum_ite, Fin.sum_univ_def]
  have hvec : table.toList = (List.finRange n).map (fun j ↦ table[j.val]) := by
    have h := congrArg Vector.toList (Vector.ofFn_getElem (xs := table))
    simpa only [Vector.toList_ofFn, List.ofFn_eq_map] using h.symm
  simpa only [hvec, List.map_map, Function.comp_def] using
    sum_ite_eq_count_mul table.toList k w

private theorem sumFiber_normalizedLookupWeights_eq (table : Vector κ n)
    (queries : Vector κ m) (k : κ) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ (normalizedLookupWeights F table queries)[j.val]) k =
      (table.toList.count k : F) *
        ((queries.toList.count k : F) / (table.toList.count k : F)) := by
  rw [← sumFiber_const_eq_count_mul]
  unfold Finset.sumFiber
  apply Finset.sum_congr rfl
  intro j hj
  have h := (Finset.mem_filter.mp hj).2
  simp only [normalizedLookupWeights, Vector.getElem_map, h]

/-- Normalized weights aggregate to query counts when lookup indices are correct and table
normalizers remain nonzero. No characteristic bound or query-count nonvanishing is assumed. -/
theorem sumFiber_normalizedLookupWeights (table : Vector κ n) (queries : Vector κ m)
    (indices : Vector (Fin n) m)
    (hlookup : ∀ i : Fin m, table[(indices[i.val]).val] = queries[i.val])
    (hnormalizers : ∀ j : Fin n, (table.toList.count table[j.val] : F) ≠ 0) (k : κ) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ (normalizedLookupWeights F table queries)[j.val]) k =
      (queries.toList.count k : F) := by
  by_cases hex : ∃ j : Fin n, table[j.val] = k
  · obtain ⟨j, hj⟩ := hex
    have hden : (table.toList.count k : F) ≠ 0 := by rw [← hj]; exact hnormalizers j
    rw [sumFiber_normalizedLookupWeights_eq, mul_div_cancel₀ _ hden]
  · have htable : ∀ j ∈ (Finset.univ : Finset (Fin n)), table[j.val] ≠ k := by
      intro j _ hj
      exact hex ⟨j, hj⟩
    have hcount : queries.toList.count k = 0 := by
      rw [← sumFiber_histogram table queries indices hlookup k]
      exact Finset.sumFiber_eq_zero_of_forall_ne _ _ _ _ htable
    rw [Finset.sumFiber_eq_zero_of_forall_ne _ _ _ _ htable, hcount, Nat.cast_zero]

/-- Normalization and the cast indexed histogram agree fiberwise, without agreeing as messages. -/
theorem sumFiber_normalizedLookupWeights_eq_histogram (table : Vector κ n)
    (queries : Vector κ m) (indices : Vector (Fin n) m)
    (hlookup : ∀ i : Fin m, table[(indices[i.val]).val] = queries[i.val])
    (hnormalizers : ∀ j : Fin n, (table.toList.count table[j.val] : F) ≠ 0) (k : κ) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ (normalizedLookupWeights F table queries)[j.val]) k =
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ ((histogram indices)[j.val] : F)) k := by
  rw [sumFiber_normalizedLookupWeights table queries indices hlookup hnormalizers,
    sumFiber_cast_histogram table queries indices hlookup]

/-- A numeric TABLE-length budget below the characteristic ensures the required normalizers.
The query length is unrestricted in this forward aggregate correspondence. -/
theorem sumFiber_normalizedLookupWeights_of_length_lt_char (p : ℕ) [CharP F p]
    (table : Vector κ n) (queries : Vector κ m) (indices : Vector (Fin n) m)
    (hlookup : ∀ i : Fin m, table[(indices[i.val]).val] = queries[i.val])
    (hbudget : n < p) (k : κ) :
    Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val])
      (fun j ↦ (normalizedLookupWeights F table queries)[j.val]) k =
      (queries.toList.count k : F) := by
  apply sumFiber_normalizedLookupWeights table queries indices hlookup
  intro j hzero
  have hpos : 0 < table.toList.count table[j.val] :=
    List.count_pos_iff.mpr (Vector.mem_toList_iff.mpr (Vector.getElem_mem j.isLt))
  have hlt : table.toList.count table[j.val] < p :=
    lt_of_le_of_lt List.count_le_length (by simpa using hbudget)
  exact Nat.not_dvd_of_pos_of_lt hpos hlt ((CharP.cast_eq_zero_iff F p _).mp hzero)
end Vector
