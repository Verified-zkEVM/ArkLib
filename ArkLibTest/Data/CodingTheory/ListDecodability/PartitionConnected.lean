/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.PartitionConnected
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for weakly partition-connected agreement hypergraphs
-/

open Code Finset

namespace ListDecodabilityPartitionConnectedTest

/-- The three words of weight one in `(Fin 2)³`. Against the zero word their agreement hypergraph
is the triangle `{0, 1}, {0, 2}, {1, 2}`. -/
private def triangleWords : Fin 3 → Fin 3 → Fin 2 := ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]

/-- Each word is at distance `1` from the zero word, so the distances sum to `3 ≤ 2 * (3 - 1)`. -/
example : ∃ S : Finset (Fin 3), 2 ≤ #S ∧
    IsWeaklyPartitionConnected (fun i : Fin 3 ↦ {j : S | triangleWords j i = 0}) 1 := by
  refine exists_isWeaklyPartitionConnected_agreement_of_sum_hammingDist_le (y := 0) (by simp) ?_
  have h : ∑ j, Δ₀((0 : Fin 3 → Fin 2), triangleWords j) = 3 := by decide
  rw [← Nat.cast_sum, h]
  norm_num

/-- The code of the three words has list size more than `2` at relative radius
`2 / 3 * (1 - 1 / 3) = 4 / 9`: the zero word is at relative distance `1 / 3` from each. -/
example : ∃ y : Fin 3 → Fin 2, ∃ s : ℕ, 1 ≤ s ∧ s ≤ 2 ∧ ∃ c : Fin (s + 1) ↪ (Fin 3 → Fin 2),
    (∀ j, c j ∈ Set.range triangleWords) ∧
      IsWeaklyPartitionConnected (fun i ↦ {j | c j i = y i}) 1 := by
  have hsub : Set.range triangleWords ⊆ closeCodewordsRel (Set.range triangleWords) 0
      (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1) * (1 - 1 / Fintype.card (Fin 3))) := by
    rintro _ ⟨j, rfl⟩
    refine mem_closeCodewordsRel_iff.2 ⟨⟨j, rfl⟩, ?_⟩
    have h : Δ₀((0 : Fin 3 → Fin 2), triangleWords j) = 1 := by fin_cases j <;> decide
    rw [relHammingDist_coe, h]
    norm_num
  have hlt : ((2 : ℕ) : ℕ∞) < Lambda (Set.range triangleWords)
      (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1) * (1 - 1 / Fintype.card (Fin 3))) := by
    refine lt_of_lt_of_le ?_ (encard_le_Lambda_of_subset_closeCodewordsRel hsub)
    have hrange : Set.range triangleWords = ↑(univ.image triangleWords) := by simp
    have hcard : #(univ.image triangleWords) = 3 := by decide
    rw [hrange, Set.encard_coe_eq_coe_finsetCard, hcard]
    exact_mod_cast (show 2 < 3 by norm_num)
  obtain ⟨y, s, hs1, hs2, c, hc, hwpc⟩ :=
    exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda (by norm_num) hlt
  exact ⟨y, s, hs1, hs2, c, fun j ↦ (mem_closeCodewordsRel_iff.1 (hc j)).1, hwpc⟩

end ListDecodabilityPartitionConnectedTest
