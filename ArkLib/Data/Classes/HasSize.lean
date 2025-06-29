/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Embedding.Basic

/-!
  # `HasSize` class
-/

/-- Type class for types that has an injective mapping to a vector of a given length `size` of
  another type (often `UInt8`). -/
class HasSize (α : Type*) (β : Type*) where
  size : Nat
  toFun : α ↪ Vector β size
