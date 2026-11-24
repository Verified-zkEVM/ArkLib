/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.Certificate
import Mathlib.Data.Rat.Defs

/-! # Certificate acceptance tests

Ten edges on two vertices, each edge joining both vertices, so all edges have the same type; with
`2 ^ 2 = 4` possible types and `r = 4`, the bank holds the largest unused edge, and with `r = 8`
the two largest. The hypergraph is exactly `10`-weakly partition-connected, that is,
`(k + 2 * r)`-weakly partition-connected for `k = 2`, `r = 4`.

Rigidity and certificates are defined at every point `α : Fin n → F`. The point used here is the
constant `0` over `ℚ`, which is not injective. At `0` the polynomials `X` and `0` of degree less
than `2` agree on every edge, so the hypergraph is not rigid for degree `2`, and it has an
injective certificate of length `4` with fewer than `4` descents. With a bank of one edge per
type, the first step of a certificate empties the bank and the second refreshes it.
-/

open Finset Polynomial ReedSolomon

private def allEdges : Fin 10 → Finset (Fin 2) := fun _ ↦ univ

example : Certificate.bank allEdges 4 [] = {9} := by decide

example : Certificate.bank allEdges 4 [9, 3] = {8} := by decide

example : Certificate.bank allEdges 8 [9] = {7, 8} := by decide

/-- Every proper vertex set of `Fin 2` has at most one vertex, and the ten edges have weight
`10`. -/
private theorem allEdges_isWeaklyPartitionConnected :
    IsWeaklyPartitionConnected allEdges (((2 : ℕ) : ℝ) + 2 * ((4 : ℕ) : ℝ)) := by
  refine isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_
  · have h : ∑ i, (#(allEdges i) - 1) = 10 := by decide
    rw [h]
    norm_num
  · exact absurd (card_lt_card hU) (by simp only [card_univ, Fintype.card_fin]; omega)

/-- The tuple `(X, 0)` agrees on every edge at the point `0`. -/
private theorem not_isRigid_zero : ¬IsRigid allEdges 2 (fun _ ↦ (0 : ℚ)) := by
  intro h
  have h0 := congrFun (h ![X, 0] (fun j ↦ ?_) rfl fun i j _ j' _ ↦ ?_) 0
  · exact X_ne_zero h0
  · fin_cases j
    · exact mem_degreeLT.2 (degree_X_le.trans_lt (by decide))
    · exact zero_mem _
  · fin_cases j <;> fin_cases j' <;> simp

example : ∃ c : Fin 4 ↪ Fin 10, #(Tuple.descents c) < 2 ^ 2 ∧
    IsCertificate ℚ allEdges_isWeaklyPartitionConnected (fun _ ↦ 0) c :=
  exists_embedding_isCertificate_of_not_isRigid not_isRigid_zero

example : ∃ c : Fin 4 ↪ Fin 10, #(Tuple.descents c) < 2 ^ 2 ∧ ∀ i ∈ univ.map c,
    MvPolynomial.aeval (fun j ↦ if j < i then MvPolynomial.C (0 : ℚ) else MvPolynomial.X j)
        (certificatePolynomial ℚ allEdges_isWeaklyPartitionConnected c i) ≠ 0 ∧
      MvPolynomial.aeval (fun j ↦ if j ≤ i then MvPolynomial.C (0 : ℚ) else MvPolynomial.X j)
        (certificatePolynomial ℚ allEdges_isWeaklyPartitionConnected c i) = 0 := by
  obtain ⟨c, hd, hc⟩ := exists_embedding_isCertificate_of_not_isRigid
    (hH := allEdges_isWeaklyPartitionConnected) not_isRigid_zero
  exact ⟨c, hd, hc.aeval_certificatePolynomial⟩
