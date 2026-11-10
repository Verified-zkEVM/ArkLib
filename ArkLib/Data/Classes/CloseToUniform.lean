/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Data.Bytes.Bias
public import CompPoly.Data.Classes.Serialize
public import Mathlib.Probability.UniformOn
public import VCVio.OracleComp.EvalDist.DiscreteTVDistFintype
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
  # Deserialization close to uniform

  The `Serialize` / `Deserialize` / `Serde` classes live in CompPoly
  (`CompPoly.Data.Classes.Serialize`), where every field and polynomial type carries instances.
  What stays here is the statistical statement, which needs measure theory: a deserializer from a
  uniformly random `β` produces an almost uniform `α`.

  CompPoly proves the counting fact behind this for its reduce-modulo-order challenge decoder:
  `CompPoly.CanonicalNat.tv_ofBytesModOrder_le` bounds the sum of absolute fiber-mass differences
  by `bound / 256 ^ n`, over `ℚ`. That sum has the same normalization as `ε_close` below, so
  `Deserialize.CloseToUniform.instOfBytesModOrder` transfers it with `ε = bound / 256 ^ n` for
  every `CanonicalNat` type, `ZMod p` included. Sixteen bytes beyond the field's width make
  `ε < 2 ^ -128`.

  All finite uniform measures use the canonical discrete measurable space internally; callers
  do not need measurable-space instances.
-/

@[expose] public section

universe u

local instance (α : Type u) : MeasurableSpace α := ⊤

open NNReal ProbabilityTheory MeasureTheory in
/-- Deserialization pushes forward the finite uniform measure within `ε` in the sum of absolute
singleton-mass differences. This retains the original L1 normalization (twice total variation).
The canonical discrete measurable spaces make every finite-space deserializer measurable. -/
class Deserialize.CloseToUniform (α : Type u) (β : Type u)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [Deserialize α β] where
  ε : ℝ≥0
  ε_close : (∑ x : α, |((uniformOn Set.univ : Measure α) {x}).toReal -
    ((uniformOn Set.univ : Measure β).map deserialize {x}).toReal|) ≤ ε

namespace Deserialize.CloseToUniform

open NNReal ProbabilityTheory MeasureTheory CompPoly CompPoly.CanonicalNat

variable {F : Type} [CanonicalNat F] [Fintype F]

/-- The measure form of `CompPoly.CanonicalNat.tv_ofBytesModOrder_le`: pushing the uniform
measure on `n`-byte strings through `ofBytesModOrder` lands within `bound / 256 ^ n` of uniform in
the sum of absolute singleton-mass differences. -/
theorem ofBytesModOrder_l1_le (n : ℕ) :
    (∑ x : F, |((uniformOn Set.univ : Measure F) {x}).toReal -
      ((uniformOn Set.univ : Measure (Vector UInt8 n)).map
        (ofBytesModOrder (F := F)) {x}).toReal|) ≤ (bound F : ℝ) / 256 ^ n := by
  classical
  have hq : ((∑ x : F, |((Fintype.card {v : Vector UInt8 n // ofBytesModOrder v = x} : ℚ) /
      256 ^ n) - 1 / bound F| : ℚ) : ℝ) ≤ ((bound F / 256 ^ n : ℚ) : ℝ) := by
    exact_mod_cast tv_ofBytesModOrder_le (F := F) n
  push_cast at hq
  refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) hq
  rw [abs_sub_comm]
  congr 1
  rw [Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete),
    uniformOn_univ, uniformOn_univ, Measure.count_singleton, Bytes.card_vector_uint8,
    card_eq]
  have hc : Measure.count (ofBytesModOrder (F := F) ⁻¹' {x} : Set (Vector UInt8 n)) =
      (Fintype.card {v : Vector UInt8 n // ofBytesModOrder v = x} : ENNReal) := by
    rw [Fintype.card_subtype, ← Measure.count_apply_finset]
    congr 1
    ext v
    simp
  rw [hc]
  simp [ENNReal.toReal_div]

/-- Every `CanonicalNat` type, in particular `ZMod p`, decodes `n` uniform bytes by
`ofBytesModOrder` to within `bound / 256 ^ n` of uniform. -/
noncomputable instance instOfBytesModOrder [Nonempty F] (n : ℕ) :
    Deserialize.CloseToUniform F (Vector UInt8 n) where
  ε := ⟨(bound F : ℝ) / 256 ^ n, by positivity⟩
  ε_close := ofBytesModOrder_l1_le n

end Deserialize.CloseToUniform

/-! ## Uniform sampling through a close-to-uniform deserializer -/

namespace Deserialize.CloseToUniform

open MeasureTheory ProbabilityTheory

section Sampling

/-- A `Deserialize.CloseToUniform` decoder is `ε / 2`-close to uniform in total variation.
The class bounds the L1 distance of the point masses, which is twice the total variation; this
is the normalization that CO25's codec bias `ε_cdc` (a total variation bound) needs. -/
theorem discreteTVDist_uniform_deserialize_le {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] [Deserialize α β]
    [h : Deserialize.CloseToUniform α β] :
    discreteTVDist ($ᵗ α) (Deserialize.deserialize <$> ($ᵗ β)) ≤ (h.ε : ℝ) / 2 := by
  unfold discreteTVDist measureTVDist
  refine (Measure.tvDist_eq_half_sum_abs _ _).le.trans
    (div_le_div_of_nonneg_right (le_of_eq_of_le ?_ h.ε_close) zero_le_two)
  rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample,
    SampleableType.evalDist_uniformSample]

end Sampling

end Deserialize.CloseToUniform
