/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Init
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Probability.UniformOn

/-!
  # Serialization and Deserialization

  This file contains simple APIs for serialization and deserialization of types in terms of other
  types.
-/

@[expose] public section

universe u v

/-- Type class for types that can be serialized to another type (most often `ByteArray` or
  `String`). -/
class Serialize (α : Type u) (β : Type v) where
  serialize : α → β

export Serialize (serialize)

/-- Type class for injective serialization. -/
class Serialize.IsInjective (α : Type u) (β : Type v) [inst : Serialize α β] : Prop where
  serialize_inj : Function.Injective inst.serialize

/-- Type class for types that can be deserialized from another type (most often `ByteArray` or
  `String`), which _never_ fails. -/
class Deserialize (α : Type u) (β : Type v) where
  deserialize : β → α

open NNReal ProbabilityTheory MeasureTheory in
/-- Deserialization pushes forward the finite uniform measure within `ε` in the sum of absolute
singleton-mass differences. This retains the original L1 normalization (twice total variation).
The discrete measurable spaces make every finite-space deserializer measurable. -/
class Deserialize.CloseToUniform (α : Type u) (β : Type u)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [Deserialize α β] where
  ε : ℝ≥0
  ε_close : (∑ x : α, |((uniformOn Set.univ : Measure α) {x}).toReal -
    ((uniformOn Set.univ : Measure β).map deserialize {x}).toReal|) ≤ ε


/-- Type class for types that can be deserialized from another type (most often `ByteArray` or
  `String`), returning an `Option` if the deserialization fails. -/
class DeserializeOption (α : Type u) (β : Type v) where
  deserialize : β → Option α

/-- Type class for types that can be serialized and deserialized (with potential failure) to/from
  another type (most often `ByteArray` or `String`). -/
class Serde (α : Type u) (β : Type v) extends Serialize α β, DeserializeOption α β

-- Note: for codecs into an alphabet `σ`, we basically want the following:
-- variable {α σ : Type*} {n : ℕ} [inst : Serialize α (Vector σ n)] [inst.IsInjective]

-- Note: for codecs out of an alphabet `σ`, we basically want the following:
-- variable {α σ : Type u} [Fintype α] [Nonempty α] [Fintype σ] [Nonempty σ] {n : ℕ} [NeZero n]
--   [inst : Deserialize α (Vector σ n)] [inst.CloseToUniform]
