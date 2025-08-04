/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Function.Defs

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

/-- A lawful `ToNat` instance where `toNat` is injective.
This ensures that different values in the original type map to different natural numbers. -/
class LawfulToNat (α : Type u) [ToNat α] : Prop where
  /-- The `toNat` function is injective. -/
  toNat_injective : Function.Injective (@ToNat.toNat α _)

-- Export the injectivity property for easier access
export LawfulToNat (toNat_injective)

-- Basic lawful instances

instance : LawfulToNat Nat where
  toNat_injective := Function.injective_id

-- Useful lemmas

namespace LawfulToNat

variable {α : Type u} [ToNat α]

/-- If two values have the same `toNat`, they are equal. -/
theorem toNat_eq_iff [LawfulToNat α] (a b : α) : ToNat.toNat a = ToNat.toNat b ↔ a = b :=
  ⟨@toNat_injective α _ _ a b, fun h => h ▸ rfl⟩

/-- If `toNat` values are different, the original values are different. -/
theorem ne_of_toNat_ne (a b : α) (h : ToNat.toNat a ≠ ToNat.toNat b) : a ≠ b :=
  fun eq => h (eq ▸ rfl)

end LawfulToNat
