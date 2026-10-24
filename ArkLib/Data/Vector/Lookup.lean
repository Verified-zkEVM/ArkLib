/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Vector.Histogram

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

end Vector
