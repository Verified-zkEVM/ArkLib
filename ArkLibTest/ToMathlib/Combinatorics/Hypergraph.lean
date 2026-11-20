/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.Combinatorics.Hypergraph.PartitionConnected
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for weakly partition-connected hypergraphs
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
