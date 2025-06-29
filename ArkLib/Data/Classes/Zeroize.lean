/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Notation.Pi

/-!
  # `Zeroize` class
-/

/-- Type class for types that can be zeroized. -/
class Zeroize (α : Type*) where
  zeroize : α → α

/-- Derive `Zeroize` from `Zero`. -/
instance {α : Type*} [Zero α] : Zeroize α where
  zeroize := Zero.zero
