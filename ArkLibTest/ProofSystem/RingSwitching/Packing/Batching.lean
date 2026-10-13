/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Batching
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Batching strategies on small concrete rings

The power-batching bound is attained by two explicit families over `ZMod 5`, and fails over the
non-domain `ZMod 6`. Reindexing, error values, and deterministic singleton batching over a ring
with zero divisors are checked numerically.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.Batching

open MvPolynomial ProbabilityTheory
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Power batching of three claims over `ZMod 5` has loss `(3 - 1)/5`. -/
theorem gammaPowers_error : (BatchingStrategy.gammaPowers (ZMod 5) 3).error = 2 / 5 := by
  simp [BatchingStrategy.gammaPowers]

/-- The bound is attained: the difference `2 + 2γ + γ² = (γ - 1)(γ - 2)` vanishes at two of the
five challenges, so the two families collide with probability exactly `2/5`. -/
theorem gammaPowers_collisions_tight :
    (Finset.univ.filter fun γ : ZMod 5 =>
      ∑ u, (BatchingStrategy.gammaPowers (ZMod 5) 3).weight γ u * ![2, 2, 1] u =
        ∑ u, (BatchingStrategy.gammaPowers (ZMod 5) 3).weight γ u * 0).card = 2 := by
  decide

/-- Off a domain the power bound fails: over `ZMod 6` the nonzero difference `3γ` vanishes at
three of six challenges, above the `(2 - 1)/6` a domain would allow. -/
theorem powers_collisions_zmod6 :
    (Finset.univ.filter fun γ : ZMod 6 =>
      ∑ u : Fin 2, γ ^ (u : ℕ) * ![0, 3] u = ∑ u : Fin 2, γ ^ (u : ℕ) * 0).card = 3 := by
  decide

/-- At the probability level the power bound is attained for these two families. -/
theorem gammaPowers_tight :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ∑ u, (BatchingStrategy.gammaPowers (ZMod 5) 3).weight γ u * ![2, 2, 1] u =
        ∑ u, (BatchingStrategy.gammaPowers (ZMod 5) 3).weight γ u * 0] =
      ((BatchingStrategy.gammaPowers (ZMod 5) 3).error : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample, gammaPowers_collisions_tight, gammaPowers_error]
  simp

/-- Over `ZMod 6` the power-batched families `(0, 3)` and `0` collide with probability `3/6`,
three times the `(2 - 1)/6` that the domain bound would give. -/
theorem powers_zmod6_probability :
    Pr{let γ ← $ᵗ (ZMod 6)}[
      ∑ u : Fin 2, γ ^ (u : ℕ) * ![0, 3] u = ∑ u : Fin 2, γ ^ (u : ℕ) * 0] = 3 / 6 := by
  rw [SampleableType.prEvent_uniformSample, powers_collisions_zmod6]
  simp

/-- Reindexing reads weights through the equivalence: reversing three power weights at `γ = 2`
puts `2² = 4` in position zero. -/
theorem reindex_weight :
    ((BatchingStrategy.gammaPowers (ZMod 5) 3).reindex Fin.revPerm).weight (2 : ZMod 5) 0 =
      4 := by
  decide

/-- Equality-fold batching of two Boolean coordinates over `ZMod 5` has loss `2/5`. -/
theorem eqFold_error : (BatchingStrategy.eqFold (ZMod 5) 2).error = 2 / 5 := by
  simp [BatchingStrategy.eqFold]

/-- A singleton claim over `ZMod 6`, which is not a domain, separates with zero error. -/
theorem singleton_separates :
    Pr{let c ← $ᵗ (BatchingStrategy.singleton (ZMod 6) Unit).Challenge}[
      ∑ u, (BatchingStrategy.singleton (ZMod 6) Unit).weight c u * (fun _ => (2 : ZMod 6)) u =
        ∑ u, (BatchingStrategy.singleton (ZMod 6) Unit).weight c u * (fun _ => 5) u] = 0 :=
  le_antisymm (((BatchingStrategy.singleton (ZMod 6) Unit).separates _ _
    fun h => absurd (congrFun h ()) (by decide)).trans_eq (by simp [BatchingStrategy.singleton]))
    zero_le

/-- Power batching of a single claim has zero loss. -/
theorem gammaPowers_one_error : (BatchingStrategy.gammaPowers (ZMod 3) 1).error = 0 := by
  simp [BatchingStrategy.gammaPowers]

/-- Equality-fold batching with no coordinates has zero loss. -/
theorem eqFold_zero_error : (BatchingStrategy.eqFold (ZMod 3) 0).error = 0 := by
  simp [BatchingStrategy.eqFold]

end RingSwitching.Packing.Tests.Batching

end
