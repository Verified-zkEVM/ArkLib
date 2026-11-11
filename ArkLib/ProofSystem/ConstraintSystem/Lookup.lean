/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Set.Defs

/-!
  # Lookup relations

-/

@[expose] public section

universe u v w

namespace Lookup

variable {α : Type u} {Value : Type v} {Table : Type w} [Membership α Value] [Membership α Table]

/-- The lookup relation. Takes in a collection of values and a table, both containers for elements
    of type `α`, and asserts that all elements in `values` are also in `table`.

  Note: this generic membership typeclass allows for multiple underlying data types for `Value` and
  `Table`, such as `List`, `Set`, `Finset`, `Array`, `Vector`, etc. -/
def relation : Set (Value × Table) := { ⟨values, table⟩ | ∀ value ∈ values, value ∈ table }

-- variants? vector lookups? batched lookups? indexed lookups (aka read-only memory checking)?

end Lookup
