/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Embedding.Basic
import Mathlib.Algebra.Notation.Pi

/-!
  # Classes for general programming / hash functions / duplex sponges

  TODO: we will refine / refactor this file as we add more classes
-/

/-- Type class for types that can be zeroized. -/
class Zeroize (α : Type*) where
  zeroize : α → α

/-- Derive `Zeroize` from `Zero`. -/
instance {α : Type*} [Zero α] : Zeroize α where
  zeroize := Zero.zero

/-- Type class for types that can be initialized from a value of type `β`.

This abstraction allows different types to be initialized from the same input type,
providing a uniform interface for construction. In the context of cryptographic sponges,
this is typically used to initialize states from a seed or initialization vector.
-/
class Initialize (α : Type*) (β : Type*) where
  /-- Initialize a value of type `α` from a value of type `β`. -/
  new : β → α

/-- Type class for types that has an injective mapping to a vector of a given length `size` of
  another type (often `UInt8`). -/
class HasSize (α : Type*) (β : Type*) where
  size : Nat
  toFun : α ↪ Vector β size
