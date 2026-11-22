/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.Combinatorics.Hypergraph.GenericZeroPattern
import ArkLib.ToMathlib.Combinatorics.Hypergraph.PartitionConnected
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for weakly partition-connected hypergraphs and their generic zero patterns
-/

open Finset

/-- The triangle on three vertices is `1`-weakly partition-connected: its weight is `3 ≥ 1 * 2`,
and every two-vertex set carries exactly one edge, of weight `1 ≤ 1 * 1`. -/
private theorem triangle_isWeaklyPartitionConnected :
    IsWeaklyPartitionConnected (![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) 1 := by
  refine isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_
  · exact_mod_cast (by decide : 1 * (Fintype.card (Fin 3) - 1) ≤
      ∑ i, (#((![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) i) - 1))
  · have key : ∀ U : Finset (Fin 3), U ≠ univ → 2 ≤ #U →
        ∑ i, (#((![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) i ∩ U) - 1) ≤ #U - 1 := by
      decide
    rw [one_mul]
    exact_mod_cast key U hU.ne hU2

/-- In the triangle every vertex lies in at least one edge. -/
example (v : Fin 3) :
    (1 : ℝ) ≤ #{i | v ∈ (![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) i} :=
  triangle_isWeaklyPartitionConnected.le_card_filter_mem v

/-- On one vertex every hypergraph, even one with no nonempty edge, is `5`-weakly
partition-connected, so the degree bound needs `Nontrivial V`. -/
example : IsWeaklyPartitionConnected (fun _ : Fin 1 ↦ (∅ : Finset (Fin 1))) 5 := by
  intro P
  have hP : #P.parts ≤ 1 := P.card_parts_le_card.trans (by simp)
  rw [Nat.sub_eq_zero_of_le hP]
  simp

/-- The triangle with the natural-number parameter `1`. -/
private theorem triangle_isWeaklyPartitionConnected' :
    IsWeaklyPartitionConnected (![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) (1 : ℕ) :=
  mod_cast triangle_isWeaklyPartitionConnected

/-- The triangle gives multiplicities of total `2` such that every nonempty vertex set `A` meets
at least `∑ j ∈ A, δ j + 1` edges. -/
example : ∃ δ : Fin 3 → ℕ, ∑ j, δ j + 1 = 3 ∧ ∀ A : Finset (Fin 3), A.Nonempty →
    ∑ j ∈ A, δ j + 1 ≤
      #{i | ((![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) i ∩ A).Nonempty} :=
  triangle_isWeaklyPartitionConnected'.exists_sum_add_eq_card (by decide) (by decide)

/-- The triangle gives two vertices whose sets of avoiding edges form a generic zero pattern. -/
example : ∃ f : Fin 2 → Fin 3,
    IsGenericZeroPattern 2 fun ℓ ↦
      {i | f ℓ ∉ (![{0, 1}, {1, 2}, {0, 2}] : Fin 3 → Finset (Fin 3)) i} :=
  triangle_isWeaklyPartitionConnected'.exists_isGenericZeroPattern (by decide)

/-- An empty edge breaks the conclusion: `{0, 1}` and `∅` form a `1`-weakly partition-connected
hypergraph, but every vertex is avoided by the empty edge, so no vertex gives a generic zero pattern
with one set. -/
example : IsWeaklyPartitionConnected (![{0, 1}, ∅] : Fin 2 → Finset (Fin 2)) 1 ∧
    ¬∃ f : Fin 1 → Fin 2,
      IsGenericZeroPattern 1 fun ℓ ↦ {i | f ℓ ∉ (![{0, 1}, ∅] : Fin 2 → Finset (Fin 2)) i} := by
  refine ⟨isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_, ?_⟩
  · exact_mod_cast (by decide : 1 * (Fintype.card (Fin 2) - 1) ≤
      ∑ i, (#((![{0, 1}, ∅] : Fin 2 → Finset (Fin 2)) i) - 1))
  · exact absurd hU2 (by have := card_lt_card hU; simp at this; omega)
  · unfold IsGenericZeroPattern
    decide
