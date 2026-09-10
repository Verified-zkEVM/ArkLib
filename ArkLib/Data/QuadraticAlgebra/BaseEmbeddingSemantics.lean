/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.BaseEmbeddingMachine

/-!
# Exact base-alphabet representation

The actual embedding program returns the ordered algebra-map image. Cardinality and membership
therefore remain those of the supplied base alphabet; no full extension-field coverage is claimed.
-/

@[expose] public section

namespace QuadraticAlgebra.BaseEmbeddingMachine

variable {F : Type*} [CommSemiring F] {a : F}

/-- Coordinate allocation agrees with the canonical scalar embedding. -/
theorem embedded_eq_map (xs : List F) :
    embedded (a := a) xs = xs.map (algebraMap F (QuadraticAlgebra F a 0)) := rfl

/-- Embedding preserves the actual number of materialized base elements. -/
theorem embedded_length (xs : List F) : (embedded (a := a) xs).length = xs.length := by
  simp [embedded]

/-- Distinct base elements remain distinct after allocation in the quadratic algebra. -/
theorem embedded_nodup (xs : List F) (h : xs.Nodup) : (embedded (a := a) xs).Nodup := by
  rw [embedded_eq_map]
  exact h.map algebraMap_injective

/-- A base scalar occurs in the output exactly when it occurs in the input. -/
theorem mem_embedded (xs : List F) (x : F) :
    algebraMap F (QuadraticAlgebra F a 0) x ∈ embedded xs ↔ x ∈ xs := by
  rw [embedded_eq_map]
  exact List.mem_map_of_injective algebraMap_injective

end QuadraticAlgebra.BaseEmbeddingMachine
