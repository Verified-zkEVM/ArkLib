/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.RankLoss
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-! # Rank-loss acceptance tests

Ten edges on the vertices `Fin 2`, all equal to `{0, 1}`, with `s = 1`, `k = 2` and `r = 4`. The
hypotheses of the two certificate counts hold with no slack: the hypergraph is exactly `10`-weakly
partition-connected, and `10 = k + 2 * r`. The single-minor count needs only `k`-weakly
partition-connected, which follows by monotonicity. Over the field `ZMod 11` the sample space of
tuples of ten pairwise distinct points is nonempty and the denominator
`Fintype.card (ZMod 11) - 10 + 1` is `2`, and the three theorems elaborate at this concrete field.
At this instance every row of the intersection matrix is `(1, X i)`, so every nonzero maximal
minor is `±(X b - X a)` for two distinct edges, no tuple of pairwise distinct points is a zero of
one, and the counted sets are empty.
-/

open Finset ReedSolomon

private instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

private def allEdges : Fin 10 → Finset (Fin 2) := fun _ ↦ univ

private def firstFour : Fin 4 ↪ Fin 10 := Fin.castLEEmb (show 4 ≤ 10 by omega)

/-- Every proper vertex set of `Fin 2` has at most one vertex, and the ten edges have weight
`10`. -/
private theorem allEdges_isWeaklyPartitionConnected :
    IsWeaklyPartitionConnected allEdges (((2 : ℕ) : ℝ) + 2 * ((4 : ℕ) : ℝ)) := by
  refine isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_
  · have h : ∑ i, (#(allEdges i) - 1) = 10 := by decide
    rw [h]
    norm_num
  · exact absurd (card_lt_card hU) (by simp only [card_univ, Fintype.card_fin]; omega)

example : Fintype.card (ZMod 11) - 10 + 1 = 2 := by rw [ZMod.card]

example : 0 < Fintype.card (Fin 10 ↪ ZMod 11) :=
  Fintype.card_pos_iff.2 (Function.Embedding.nonempty_of_card_le (by simp [ZMod.card]))

open Classical in
example : #{α : Fin 10 ↪ ZMod 11 | ¬IsRigid allEdges 2 α} * (Fintype.card (ZMod 11) - 10 + 1) ≤
    10 * (1 * (2 - 1)) * Fintype.card (Fin 10 ↪ ZMod 11) :=
  card_filter_not_isRigid_mul_le (allEdges_isWeaklyPartitionConnected.mono (by norm_num))

open Classical in
example : #{α : Fin 10 ↪ ZMod 11 |
      IsCertificate (ZMod 11) allEdges_isWeaklyPartitionConnected α firstFour} *
        (Fintype.card (ZMod 11) - 10 + 1) ^ 4 ≤
      (1 * (2 - 1)) ^ 4 * Fintype.card (Fin 10 ↪ ZMod 11) :=
  card_filter_isCertificate_mul_pow_le allEdges_isWeaklyPartitionConnected firstFour

open Classical in
example : #{α : Fin 10 ↪ ZMod 11 | ¬IsRigid allEdges 2 α} *
      (Fintype.card (ZMod 11) - 10 + 1) ^ 4 ≤
    Nat.choose 10 4 * (2 ^ 2) ^ 4 * (1 * (2 - 1)) ^ 4 * Fintype.card (Fin 10 ↪ ZMod 11) :=
  card_filter_not_isRigid_mul_pow_le allEdges_isWeaklyPartitionConnected
