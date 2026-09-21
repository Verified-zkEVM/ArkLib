/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Data.Classes.Serialize
public import Mathlib.Probability.Distributions.Uniform

/-!
  # Deserialization close to uniform

  The `Serialize` / `Deserialize` / `Serde` classes now live in CompPoly
  (`CompPoly.Data.Classes.Serialize`), where every field and polynomial type carries instances.
  What stays here is the statistical statement, which needs `PMF`: a deserializer from a
  uniformly random `β` produces an almost uniform `α`.

  CompPoly proves the counting fact behind this for its reduce-modulo-order challenge decoder
  (`CompPoly.CanonicalNat.tv_ofBytesModOrder_le`, a total-variation bound over `ℚ`); the
  `CloseToUniform` instances for its fields are to be derived from that bound.
-/

@[expose] public section

universe u

-- Local instance for now, will need to develop statistical distance a lot more
instance {α : Type*} [Fintype α] : Dist (PMF α) where
  dist := fun a b => ∑ x, abs ((a x).toReal - (b x).toReal)

open NNReal in
/-- Type class for deserialization on two non-empty finite types `α`, `β`, which pushes forward the
  uniform distribution of `β` to the uniform distribution of `α`, up to some error -/
class Deserialize.CloseToUniform (α : Type u) (β : Type u)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [Deserialize α β] where
  ε : ℝ≥0
  ε_close : dist (PMF.uniformOfFintype α) (deserialize <$> PMF.uniformOfFintype β) ≤ ε
