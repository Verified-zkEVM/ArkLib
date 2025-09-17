/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

-- Note: Zero.Zero seems to come from Init.Prelude so we could maybe do without the Mathlib import here?
import Mathlib.Algebra.Notation.Pi.Basic

/-!
  # `Zeroize` class
-/

/-- Type class for types that can be zeroized. -/
class Zeroize (α : Type*) where
  zeroize : α → α

/-- Derive `Zeroize` from `Zero`. -/
instance {α : Type*} [Zero α] : Zeroize α where
  zeroize := Zero.zero
