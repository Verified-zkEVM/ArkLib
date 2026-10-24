/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Fin.ConsecutiveChunks
import Lean.Compiler.IR

/-! Acceptance checks for checked consecutive index chunks. -/

namespace ConsecutiveChunks.Test

/-- An executable external caller exposes the checked typed group vector. -/
def chunksCaller (T ell : ℕ) : Option (Vector (List (Fin T)) (T ⌈/⌉ ell)) :=
  Fin.consecutiveChunks? T ell

/-- Discard index proofs for a readable finite acceptance result. -/
def indexLists {T K : ℕ} (groups : Vector (List (Fin T)) K) : List (List ℕ) :=
  groups.toList.map (List.map Fin.val)

example : chunksCaller 0 0 = none := by decide
example : chunksCaller 0 1 = none := by decide
example : chunksCaller 4 0 = none := by decide
example : chunksCaller 4 5 = none := by decide
example : (chunksCaller 1 1).map indexLists = some [[0]] := by decide
example : (chunksCaller 4 1).map indexLists = some [[0], [1], [2], [3]] := by decide
example : (chunksCaller 4 4).map indexLists = some [[0, 1, 2, 3]] := by decide
example : (chunksCaller 6 2).map indexLists = some [[0, 1], [2, 3], [4, 5]] := by decide
example : (chunksCaller 7 3).map indexLists = some [[0, 1, 2], [3, 4, 5], [6]] := by decide

/-- A concrete nondivisible partition used to exercise its proved contracts. -/
def sevenGroups : Vector (List (Fin 7)) 3 := #v[[0, 1, 2], [3, 4, 5], [6]]

theorem sevenGroups_ok : Fin.consecutiveChunks? 7 3 = some sevenGroups := by decide

example : sevenGroups.toList.flatten = List.finRange 7 :=
  Fin.flatten_of_consecutiveChunks?_eq_some sevenGroups_ok

example (i : Fin 7) : sevenGroups.toList.flatten.count i = 1 :=
  Fin.count_flatten_of_consecutiveChunks?_eq_some sevenGroups_ok i

example : sevenGroups.toList.Pairwise List.Disjoint :=
  (Fin.nodup_disjoint_of_consecutiveChunks?_eq_some sevenGroups_ok).2

example : sevenGroups[0].length = 3 :=
  Fin.length_getElem_eq_size_of_not_last sevenGroups_ok 0 (by decide)

example : sevenGroups[2].length = 1 := by
  exact (Fin.length_getElem_eq_remainder_of_last sevenGroups_ok 2 (by decide)).trans (by decide)

example : sevenGroups[2].length < 3 :=
  Fin.length_getElem_lt_size_of_last_of_not_dvd sevenGroups_ok 2 (by decide) (by decide)

#eval (chunksCaller 7 3).map indexLists

-- Many small blocks and one long block exercise both runtime extraction boundaries.
#eval (chunksCaller 100000 1).map fun groups ↦
  groups.toList.foldl (fun count group ↦ count + group.length) 0
#eval (chunksCaller 100000 100000).map fun groups ↦
  groups.toList.foldl (fun count group ↦ count + group.length) 0

open Lean Elab Command

run_cmd do
  for n in #[``Fin.consecutiveChunks?, ``chunksCaller, ``indexLists] do
    unless (Lean.IR.findEnvDecl (← getEnv) n).isSome do
      throwError "Expected compiler IR for `{n}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``List.takeList_fst_eq_splitLengths, ``List.getElem_splitLengths_replicate,
      ``Fin.consecutiveChunks?_eq_none_iff, ``Fin.flatten_of_consecutiveChunks?_eq_some,
      ``Fin.nodup_disjoint_of_consecutiveChunks?_eq_some,
      ``Fin.length_getElem_of_consecutiveChunks?_eq_some,
      ``Fin.length_getElem_pos_of_consecutiveChunks?_eq_some,
      ``Fin.length_getElem_eq_size_of_not_last,
      ``Fin.length_getElem_eq_remainder_of_last,
      ``Fin.length_getElem_lt_size_of_last_of_not_dvd,
      ``Fin.count_flatten_of_consecutiveChunks?_eq_some] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "`{n}` depends on unexpected axioms: {axioms}"

end ConsecutiveChunks.Test
