/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Fin.ConsecutiveChunks

/-!
# Checked configuration for scalar LogUp

The row-variable count is unrestricted, including zero. Column grouping accepts precisely the
successful existing consecutive-chunk construction. The proof-only certificate supplies ordered
coverage and group-size bounds to the algebraic protocol views. Generic weighted balance imposes
no characteristic or field-cardinality restriction on this configuration.
-/

@[expose] public section

namespace Logup.Interaction

/-- Runtime grouping data accompanied by the exact successful construction certificate. -/
structure Config (n T ell : ℕ) where
  /-- Consecutive column groups, with a possibly shorter final group. -/
  groups : Vector (List (Fin T)) (T ⌈/⌉ ell)
  /-- The groups are exactly those returned by the executable checked constructor. -/
  checked : Fin.consecutiveChunks? T ell = some groups

/-- Check the requested group size once and retain the resulting grouping certificate. -/
def Config.create? (n T ell : ℕ) : Option (Config n T ell) :=
  match h : Fin.consecutiveChunks? T ell with
  | none => none
  | some groups => some ⟨groups, h⟩

/-- Successful configuration accepts exactly positive totals and valid group sizes. -/
theorem Config.isSome_create? (n T ell : ℕ) :
    (Config.create? n T ell).isSome ↔ 0 < T ∧ 1 ≤ ell ∧ ell ≤ T := by
  rw [← Fin.isSome_consecutiveChunks? T ell]
  unfold Config.create?
  split <;> simp_all

/-- Flattening the configured groups preserves every column in its original order. -/
theorem Config.flatten_groups {n T ell : ℕ} (cfg : Config n T ell) :
    cfg.groups.toList.flatten = List.finRange T :=
  Fin.flatten_of_consecutiveChunks?_eq_some cfg.checked

/-- Every configured group respects the requested maximum length. -/
theorem Config.length_group_le {n T ell : ℕ} (cfg : Config n T ell) (k : Fin (T ⌈/⌉ ell)) :
    cfg.groups[k.val].length ≤ ell :=
  Fin.length_getElem_le_of_consecutiveChunks?_eq_some cfg.checked k

/-- A valid configuration has at least one column. -/
theorem Config.total_pos {n T ell : ℕ} (cfg : Config n T ell) : 0 < T := by
  have h : (Fin.consecutiveChunks? T ell).isSome := by rw [cfg.checked]; rfl
  exact ((Fin.isSome_consecutiveChunks? T ell).mp h).1

/-- A valid configuration has at least one group. -/
theorem Config.group_count_pos {n T ell : ℕ} (cfg : Config n T ell) : 0 < T ⌈/⌉ ell :=
  Fin.groupCount_pos_of_consecutiveChunks?_eq_some cfg.checked

end Logup.Interaction
