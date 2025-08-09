/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Function.Defs
import ArkLib.Data.Classes.HasSucc

universe u

/-!
# ToNat Type Class

This file defines the `ToNat` type class for converting values to natural numbers.
This provides a uniform interface for extracting natural number representations
from various types in the CNat hierarchy.
-/

/-- Type class for converting values to natural numbers. -/
class ToNat (α : Type u) where
  /-- Convert a value to a natural number. -/
  toNat : α → Nat

-- Basic instances

instance : ToNat Nat where
  toNat := id

instance {α : Type u} [ToNat α] : CoeHead α Nat where
  coe := ToNat.toNat

-- Lawful ToNat classes

/-- A `ToNat` instance on a type `α` having zero and successor is **lawful** if `toNat` maps zero to
  zero and commutes with successor. -/
class LawfulToNat (α : Type u) [ToNat α] [Zero α] [HasSucc α] : Prop where
  toNat_zero : ToNat.toNat (0 : α) = 0
  toNat_succ (n : α) : ToNat.toNat (succ' n) = ToNat.toNat n + 1

-- Export the injectivity property for easier access
export LawfulToNat (toNat_zero toNat_succ)

-- Basic lawful instances

instance : LawfulToNat Nat where
  toNat_zero := rfl
  toNat_succ := fun _ => rfl

-- Useful lemmas

namespace LawfulToNat

variable {α : Type u} [ToNat α] [Zero α] [HasSucc α] [LawfulToNat α]

-- toNat is injective

-- theorem toNat_injective : Function.Injective (@ToNat.toNat α _ _) := fun a b h => by
--   induction a using Nat.recOn with
--   | zero =>
--     simp [toNat_zero] at h
--     simp [h]
--   | succ n ih =>
--     simp [toNat_succ] at h
--     simp [h, ih]

-- /-- If two values have the same `toNat`, they are equal. -/
-- theorem toNat_eq_iff [LawfulToNat α] (a b : α) : ToNat.toNat a = ToNat.toNat b ↔ a = b :=
--   ⟨fun h => by
--     induction a using Nat.recOn with
--     | zero =>
--       simp [toNat_zero] at h
--       simp [h]
--     | succ n ih =>
--       simp [toNat_succ] at h
--       simp [h, ih]⟩
--   fun h => by
--     induction a using Nat.recOn with
--     | zero =>
--       simp [toNat_zero]
--       simp [h]
--     | succ n ih =>
--       simp [toNat_succ] at h
--       simp [h, ih]⟩

-- /-- If `toNat` values are different, the original values are different. -/
-- theorem ne_of_toNat_ne (a b : α) (h : ToNat.toNat a ≠ ToNat.toNat b) : a ≠ b :=
--   fun eq => h (eq ▸ rfl)

end LawfulToNat
