/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Set.Defs

/-!
  # Lookup relations

-/

universe u v w

namespace Lookup

variable {α : Type u} {Value : Type v} {Table : Type w} [Membership α Value] [Membership α Table]

/-- The lookup relation. Takes in a collection of values and a table, both containers for elements
    of type `α`, and asserts that all elements in `values` are also in `table`.

  Note: this generic membership typeclass allows for multiple underlying data types for `Value` and
  `Table`, such as `List`, `Set`, `Finset`, `Array`, `Vector`, etc. -/
def relation : Set (Value × Table) := { ⟨values, table⟩ | ∀ value ∈ values, value ∈ table }

-- variants? vector lookups? batched lookups? indexed lookups (aka read-only memory checking)?

-- old stuff
-- def BatchedLookupRelation (n m : ℕ+) : Relation where
--   Statement := Fin n → List R
--   Witness := (Fin m → List R) × Matrix (Fin m) (Fin n) Bool
--   isValid := fun stmt wit =>
--     ∀ i : Fin m, ∀ j : Fin n,
--       if wit.2 i j then stmt j ⊆ wit.1 i else True

end Lookup
