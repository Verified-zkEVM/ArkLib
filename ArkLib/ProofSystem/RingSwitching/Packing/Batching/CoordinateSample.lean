/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Batching

/-!
# Coordinate sampling for batching over commutative rings

Uniformly sample one coordinate and check that coordinate. Distinct families agree on at most
all but one coordinate, giving error `(rank - 1) / rank` over any commutative ring. This strategy
uses no polynomial root bound and therefore applies to rings with zero divisors.
-/

@[expose] public section

noncomputable section

namespace RingSwitching.Packing.BatchingStrategy

open Probability ProbabilityTheory
open scoped NNReal ENNReal

/-- Checking one uniformly sampled coordinate separates distinct claim families with error
`(card W - 1) / card W` over a commutative ring. -/
def coordinateSample (C W : Type) [CommRing C] [Fintype W] [DecidableEq W]
    [SampleableType W] : BatchingStrategy C W where
  Challenge := W
  weight c u := if u = c then 1 else 0
  error := ((Fintype.card W - 1 : ℕ) : ℝ≥0) / (Fintype.card W : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    have hev : ∀ c : W, ((∑ u, (if u = c then (1 : C) else 0) * s u =
        ∑ u, (if u = c then (1 : C) else 0) * s' u) ↔ s c = s' c) := by
      intro c; simp
    simp_rw [hev]
    rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast]
    rw [SampleableType.prEvent_uniformSample_le_div_iff]
    have hsub : (Finset.univ.filter fun c => s c = s' c) ⊆ Finset.univ.erase u₀ := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact Finset.mem_erase.mpr ⟨fun h => hu₀ (h ▸ hc), Finset.mem_univ _⟩
    calc (Finset.univ.filter fun c => s c = s' c).card ≤ (Finset.univ.erase u₀).card :=
          Finset.card_le_card hsub
      _ = Fintype.card W - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl

end RingSwitching.Packing.BatchingStrategy

end
