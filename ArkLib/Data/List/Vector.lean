/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Vector.Basic

/-!
# Definitions and lemmas for `List.Vector`

This file is currently not used anywhere in ArkLib. May delete in the future.
-/


namespace List

namespace Vector

variable {α : Type*}

def interleave {n : Nat} (xs : Vector α n) (ys : Vector α n) : Vector α (2 * n) := sorry

-- def pairwise {α : Type} {n : Nat} (v : Vector α (2 * n)) : Vector (α × α) n :=
--   Vector.ofFn (fun i =>
--     let j := 2 * i
--     (v.get ⟨j, by omega; exact i.isLt⟩,
--      v.get ⟨j + 1, by simp [Nat.mul_two, Nat.lt_succ]; exact i.isLt⟩))

def chunkPairwise {α : Type} : {n : Nat} → Vector α (2 * n) → Vector (α × α) n
  | 0, Vector.nil => Vector.nil
  | n + 1, xs => by
    have : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [this] at xs
    exact ⟨xs.head, xs.tail.head⟩ ::ᵥ chunkPairwise xs.tail.tail

end Vector

end List
