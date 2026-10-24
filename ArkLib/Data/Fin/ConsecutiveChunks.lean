/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToMathlib.List.SplitLengths
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.List.Nodup

/-!
# Checked consecutive chunks of finite indices

`Fin.consecutiveChunks?` splits the indices below `T` into consecutive blocks of size at most
`ell`. It accepts exactly `1 ≤ ell ≤ T`, returning a vector of `T ⌈/⌉ ell` blocks. The last block
may be shorter. Successful construction preserves the full ordered index list, so each index
occurs exactly once.

The constructor uses Batteries' `List.takeList`, whose existing theorem-backed compiler
replacement is tail-recursive. Correctness reuses Mathlib's `List.splitLengths` through the
proved bridge between these operations.
-/

@[expose] public section

namespace Fin

/-- Construct consecutive index blocks, rejecting zero or oversized requested block lengths. -/
def consecutiveChunks? (T ell : ℕ) : Option (Vector (List (Fin T)) (T ⌈/⌉ ell)) :=
  if 0 < ell ∧ ell ≤ T then
    some ⟨((List.finRange T).takeList (List.replicate (T ⌈/⌉ ell) ell)).1.toArray,
      by simp [List.takeList_fst_eq_splitLengths]⟩
  else none

/-- Construction succeeds exactly for a positive total and a valid positive block length. -/
theorem isSome_consecutiveChunks? (T ell : ℕ) :
    (consecutiveChunks? T ell).isSome ↔ 0 < T ∧ 1 ≤ ell ∧ ell ≤ T := by
  simp only [consecutiveChunks?]
  split <;> simp_all <;> omega

/-- Construction rejects exactly zero or oversized requested block lengths. -/
@[simp]
theorem consecutiveChunks?_eq_none_iff (T ell : ℕ) :
    consecutiveChunks? T ell = none ↔ ell = 0 ∨ T < ell := by
  simp [consecutiveChunks?]
  omega

private theorem valid_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) : 0 < ell ∧ ell ≤ T := by
  by_cases hv : 0 < ell ∧ ell ≤ T
  · exact hv
  · simp [consecutiveChunks?, hv] at h

/-- Successful construction agrees with consecutive extraction of the full finite index list. -/
theorem toList_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) :
    groups.toList = (List.replicate (T ⌈/⌉ ell) ell).splitLengths (List.finRange T) := by
  unfold consecutiveChunks? at h
  split at h
  · cases h
    simp [List.takeList_fst_eq_splitLengths]
  · contradiction

/-- Every source index is retained in its original order. -/
theorem flatten_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) :
    groups.toList.flatten = List.finRange T := by
  rw [toList_of_consecutiveChunks?_eq_some h]
  apply List.flatten_splitLengths
  simpa [Nat.mul_comm] using le_smul_ceilDiv (valid_of_consecutiveChunks?_eq_some h).1 (b := T)

/-- Each index appears exactly once in the flattened groups. -/
theorem nodup_flatten_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) : groups.toList.flatten.Nodup := by
  rw [flatten_of_consecutiveChunks?_eq_some h]
  exact List.nodup_finRange T

/-- Different groups are disjoint, and each group has no repeated indices. -/
theorem nodup_disjoint_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) :
    (∀ group ∈ groups.toList, group.Nodup) ∧ groups.toList.Pairwise List.Disjoint := by
  exact List.nodup_flatten.mp (nodup_flatten_of_consecutiveChunks?_eq_some h)

/-- A group contains its requested size or precisely the remaining source indices. -/
theorem length_getElem_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (g : Fin (T ⌈/⌉ ell)) :
    groups[g.val].length = min ell (T - g.val * ell) := by
  simpa only [← toList_of_consecutiveChunks?_eq_some h, Vector.getElem_toList,
    List.length_finRange] using
    List.length_getElem_splitLengths_replicate (List.finRange T)
      (T ⌈/⌉ ell) ell g.val g.isLt

/-- Successful construction has at least one group. -/
theorem groupCount_pos_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) : 0 < T ⌈/⌉ ell := by
  have hv := valid_of_consecutiveChunks?_eq_some h
  have hcover := le_smul_ceilDiv hv.1 (b := T)
  by_contra hzero
  have hK : T ⌈/⌉ ell = 0 := by omega
  simp [hK] at hcover
  omega

private theorem start_lt_total {T ell g : ℕ} (hell : 0 < ell) (hg : g < T ⌈/⌉ ell) :
    g * ell < T := by
  have hnot : ¬ T ≤ ell * g := by
    intro hle
    exact (Nat.not_le_of_lt hg) ((ceilDiv_le_iff_le_mul hell).mpr hle)
  simpa [Nat.mul_comm] using Nat.lt_of_not_ge hnot

/-- Every returned block is nonempty. -/
theorem length_getElem_pos_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (g : Fin (T ⌈/⌉ ell)) :
    0 < groups[g.val].length := by
  rw [length_getElem_of_consecutiveChunks?_eq_some h g]
  have hell := (valid_of_consecutiveChunks?_eq_some h).1
  exact lt_min hell (Nat.sub_pos_of_lt (start_lt_total hell g.isLt))

/-- Every returned block has at most the requested number of indices. -/
theorem length_getElem_le_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (g : Fin (T ⌈/⌉ ell)) :
    groups[g.val].length ≤ ell := by
  rw [length_getElem_of_consecutiveChunks?_eq_some h g]
  exact min_le_left _ _

/-- Every block before the final block has the full requested size. -/
theorem length_getElem_eq_size_of_not_last {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (g : Fin (T ⌈/⌉ ell))
    (hnotlast : g.val + 1 < T ⌈/⌉ ell) : groups[g.val].length = ell := by
  rw [length_getElem_of_consecutiveChunks?_eq_some h g]
  apply min_eq_left
  have hnext := start_lt_total (valid_of_consecutiveChunks?_eq_some h).1 hnotlast
  rw [Nat.add_mul, one_mul] at hnext
  omega

/-- The final block has exactly the number of indices remaining after all full blocks. -/
theorem length_getElem_eq_remainder_of_last {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (g : Fin (T ⌈/⌉ ell))
    (hlast : g.val + 1 = T ⌈/⌉ ell) : groups[g.val].length = T - g.val * ell := by
  rw [length_getElem_of_consecutiveChunks?_eq_some h g]
  apply min_eq_right
  have hcover := le_smul_ceilDiv (valid_of_consecutiveChunks?_eq_some h).1 (b := T)
  change T ≤ ell * (T ⌈/⌉ ell) at hcover
  rw [← hlast, Nat.mul_add, Nat.mul_one, Nat.mul_comm ell g.val] at hcover
  omega

/-- If the requested size does not divide the total, the final block is strictly shorter. -/
theorem length_getElem_lt_size_of_last_of_not_dvd {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (g : Fin (T ⌈/⌉ ell))
    (hlast : g.val + 1 = T ⌈/⌉ ell) (hnotdvd : ¬ ell ∣ T) :
    groups[g.val].length < ell := by
  have hle := length_getElem_le_of_consecutiveChunks?_eq_some h g
  have hrem := length_getElem_eq_remainder_of_last h g hlast
  have hstart := start_lt_total (valid_of_consecutiveChunks?_eq_some h).1 g.isLt
  apply lt_of_le_of_ne hle
  intro heq
  have htotal : T = ell * (g.val + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm ell g.val]
    omega
  exact hnotdvd ⟨g.val + 1, htotal⟩

/-- Each source index occurs once, rather than merely belonging to some block. -/
theorem count_flatten_of_consecutiveChunks?_eq_some {T ell : ℕ}
    {groups : Vector (List (Fin T)) (T ⌈/⌉ ell)}
    (h : consecutiveChunks? T ell = some groups) (i : Fin T) :
    groups.toList.flatten.count i = 1 := by
  rw [flatten_of_consecutiveChunks?_eq_some h]
  exact (List.nodup_finRange T).count_of_mem (List.mem_finRange i)

end Fin
