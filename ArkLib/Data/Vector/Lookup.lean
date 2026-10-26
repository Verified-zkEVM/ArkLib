/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Vector.Histogram
public import ArkLib.ToMathlib.List.Count
public import Init.Data.Vector.Perm

/-!
# Indexed lookup from weighted key fibers

A weighted table represents every queried key if its fiber weights equal the natural query counts
cast into the coefficient type, provided positive query counts remain nonzero after casting.
The coefficient type needs only an additive commutative monoid with a natural-number cast. There
is no restriction on table weights, table duplicates, or the size of the key type.
-/

@[expose] public section

namespace Vector

/-- Equality of table fiber weights with cast query counts implies a matching table index for
every query, when no positive query count becomes zero under the cast. -/
theorem exists_getElem_eq_of_sumFiber_eq_count {κ R : Type*} [DecidableEq κ]
    [AddCommMonoidWithOne R] {n m : ℕ} (table : Vector κ n) (queries : Vector κ m)
    (weights : Fin n → R)
    (hbalanced : ∀ k, Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val]) weights k =
      (queries.toList.count k : R))
    (hnonzero : ∀ k, 0 < queries.toList.count k → (queries.toList.count k : R) ≠ 0)
    (i : Fin m) : ∃ j : Fin n, table[j.val] = queries[i.val] := by
  by_contra hmissing
  have hzero : Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val]) weights
      queries[i.val] = 0 := by
    apply Finset.sumFiber_eq_zero_of_forall_ne
    intro j _ hj
    exact hmissing ⟨j, hj⟩
  have hpos : 0 < queries.toList.count queries[i.val] :=
    List.count_pos_iff.mpr (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))
  exact hnonzero queries[i.val] hpos ((hbalanced queries[i.val]).symm.trans hzero)

/-- A numeric query-length budget below the characteristic discharges the nonvanishing-count
premise of the lookup converse. The characteristic is an explicit parameter. -/
theorem exists_getElem_eq_of_sumFiber_eq_count_of_length_lt_char {κ R : Type*}
    [DecidableEq κ] [AddCommMonoidWithOne R] (p : ℕ) [CharP R p] {n m : ℕ}
    (table : Vector κ n) (queries : Vector κ m) (weights : Fin n → R)
    (hbalanced : ∀ k, Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val]) weights k =
      (queries.toList.count k : R))
    (hbudget : m < p) (i : Fin m) : ∃ j : Fin n, table[j.val] = queries[i.val] := by
  apply exists_getElem_eq_of_sumFiber_eq_count table queries weights hbalanced
  intro k hpos hzero
  have hcount : queries.toList.count k < p :=
    lt_of_le_of_lt List.count_le_length (by simpa using hbudget)
  exact Nat.not_dvd_of_pos_of_lt hpos hcount ((CharP.cast_eq_zero_iff R p _).mp hzero)

/-- In characteristic zero, positive query counts never disappear under the natural-number
cast, so the lookup converse requires no finite query-length budget. -/
theorem exists_getElem_eq_of_sumFiber_eq_count_of_charZero {κ R : Type*}
    [DecidableEq κ] [AddCommMonoidWithOne R] [CharZero R] {n m : ℕ}
    (table : Vector κ n) (queries : Vector κ m) (weights : Fin n → R)
    (hbalanced : ∀ k, Finset.univ.sumFiber (fun j : Fin n ↦ table[j.val]) weights k =
      (queries.toList.count k : R))
    (i : Fin m) : ∃ j : Fin n, table[j.val] = queries[i.val] := by
  apply exists_getElem_eq_of_sumFiber_eq_count table queries weights hbalanced
  intro k hpos
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)

/-- An injective natural-number cast recovers exact vector permutation from cast key counts. -/
theorem perm_of_cast_count_eq {κ R : Type*} [DecidableEq κ] [NatCast R] {n : ℕ}
    (xs ys : Vector κ n) (hinj : Function.Injective (Nat.cast : ℕ → R))
    (hcounts : ∀ k, (xs.toList.count k : R) = (ys.toList.count k : R)) : xs.Perm ys := by
  exact Perm.of_toList_perm (List.perm_of_cast_count_eq xs.toList ys.toList hinj hcounts)

/-- A numeric length budget below the characteristic makes cast count equality sufficient
for exact vector permutation, without a finite key type or cancellation assumption. -/
theorem perm_of_cast_count_eq_of_length_lt_char {κ R : Type*} [DecidableEq κ]
    [AddMonoidWithOne R] (p : ℕ) [CharP R p] {n : ℕ} (xs ys : Vector κ n)
    (hbudget : n < p)
    (hcounts : ∀ k, (xs.toList.count k : R) = (ys.toList.count k : R)) : xs.Perm ys := by
  exact Perm.of_toList_perm (List.perm_of_cast_count_eq_of_length_lt_char p xs.toList ys.toList
    (by simpa using hbudget) (by simpa using hbudget) hcounts)

end Vector
