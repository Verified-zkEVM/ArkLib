/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Data.Classes.Serialize
public import Mathlib.Probability.UniformOn

/-!
  # Deserialization close to uniform

  The `Serialize` / `Deserialize` / `Serde` classes live in CompPoly
  (`CompPoly.Data.Classes.Serialize`), where every field and polynomial type carries instances.
  What stays here is the statistical statement, which needs measure theory: a deserializer from a
  uniformly random `β` produces an almost uniform `α`.

  CompPoly proves the counting fact behind this for its reduce-modulo-order challenge decoder
  (`CompPoly.CanonicalNat.tv_ofBytesModOrder_le`, a total-variation bound over `ℚ`). The
  `CloseToUniform` instances for its fields are to be derived from that bound; note that `ε` here
  bounds the L1 distance, which is twice the total variation.
-/

@[expose] public section

universe u

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
