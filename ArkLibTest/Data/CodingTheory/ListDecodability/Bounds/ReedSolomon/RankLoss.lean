/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.RankLoss
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree
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

A second instance has a nonempty counted set. Six edges on the vertices `Fin 3`: two copies each
of `{0, 2}`, `{1, 2}` and `{0, 1}`, with `s = 2` and `k = 3`; the hypergraph is `3`-weakly
partition-connected. At the pairwise distinct points `0, 1, 2, 3, 4, 6` of `ZMod 7` the tuple
`(2 * X * (X - 1), 5 * (X - 2) * (X - 3), 0)` of polynomials of degree less than `3` agrees on
every edge, so the hypergraph is not rigid there.
-/

open Finset Polynomial ReedSolomon

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

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private def sixEdges : Fin 6 → Finset (Fin 3) := ![{0, 2}, {0, 2}, {1, 2}, {1, 2}, {0, 1}, {0, 1}]

/-- The six edges have weight `6 = 3 * 2`, and every two-vertex set carries two edges, of weight
`2 ≤ 3 * 1`. -/
private theorem sixEdges_isWeaklyPartitionConnected :
    IsWeaklyPartitionConnected sixEdges ((3 : ℕ) : ℝ) := by
  refine isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_
  · exact_mod_cast (by decide : 3 * (Fintype.card (Fin 3) - 1) ≤ ∑ i, (#(sixEdges i) - 1))
  · have key : ∀ U : Finset (Fin 3), U ≠ univ → 2 ≤ #U →
        ∑ i, (#(sixEdges i ∩ U) - 1) ≤ 3 * (#U - 1) := by
      decide
    exact_mod_cast key U hU.ne hU2

private def sixPoints : Fin 6 ↪ ZMod 7 := ⟨![0, 1, 2, 3, 4, 6], by decide⟩

/-- The tuple `(2 * X * (X - 1), 5 * (X - 2) * (X - 3), 0)` agrees on every edge at `sixPoints`. -/
private theorem not_isRigid_sixPoints : ¬IsRigid sixEdges 3 (sixPoints : Fin 6 → ZMod 7) := by
  intro h
  set f : Fin 3 → (ZMod 7)[X] := ![C 2 * X * (X - 1), C 5 * (X - C 2) * (X - C 3), 0]
  have hf (j : Fin 3) (x : ZMod 7) :
      (f j).eval x = ![2 * x * (x - 1), 5 * (x - 2) * (x - 3), 0] j := by
    fin_cases j <;> simp [f]
  have key : ∀ i, ∀ j ∈ sixEdges i, ∀ j' ∈ sixEdges i,
      (![2 * sixPoints i * (sixPoints i - 1), 5 * (sixPoints i - 2) * (sixPoints i - 3), 0] j :
        ZMod 7) = ![2 * sixPoints i * (sixPoints i - 1), 5 * (sixPoints i - 2) * (sixPoints i - 3),
          0] j' := by
    decide
  have h0 := congrFun (h f (fun j ↦ ?_) rfl fun i j hj j' hj' ↦ ?_) 0
  · have := congrArg (eval (2 : ZMod 7)) h0
    rw [hf, Pi.zero_apply, eval_zero] at this
    exact absurd this (by decide)
  · fin_cases j
    · rw [mem_degreeLT]
      exact (show (C 2 * X * (X - 1) : (ZMod 7)[X]).degree ≤ 2 by compute_degree).trans_lt
        (by decide)
    · rw [mem_degreeLT]
      exact (show (C 5 * (X - C 2) * (X - C 3) : (ZMod 7)[X]).degree ≤ 2 by compute_degree).trans_lt
        (by decide)
    · exact zero_mem _
  · rw [hf, hf]
    exact key i j hj j' hj'

open Classical in
example : 0 < #{α : Fin 6 ↪ ZMod 7 | ¬IsRigid sixEdges 3 α} :=
  card_pos.2 ⟨sixPoints, mem_filter.2 ⟨mem_univ _, not_isRigid_sixPoints⟩⟩

open Classical in
example : #{α : Fin 6 ↪ ZMod 7 | ¬IsRigid sixEdges 3 α} * (Fintype.card (ZMod 7) - 6 + 1) ≤
    6 * (2 * (3 - 1)) * Fintype.card (Fin 6 ↪ ZMod 7) :=
  card_filter_not_isRigid_mul_le sixEdges_isWeaklyPartitionConnected
