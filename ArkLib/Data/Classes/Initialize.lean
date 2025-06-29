/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Init

/-!
  # `Initialize` class
-/

universe u v

/-- Type class for types that can be initialized from a value of type `β`.

This abstraction allows different types to be initialized from the same input type,
providing a uniform interface for construction. In the context of cryptographic sponges,
this is typically used to initialize states from a seed or initialization vector.
-/
class Initialize (α : Type u) (β : Type v) where
  /-- Initialize a value of type `α` from a value of type `β`. -/
  new : β → α
