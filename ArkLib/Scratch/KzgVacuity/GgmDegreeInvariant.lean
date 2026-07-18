/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import Mathlib

/-!
# Structural degree invariant for the generic-group handle table

The `GgmAdaptive` file proves the adaptive generic group model [Sho97] $t$-SDH bound under two
external degree hypotheses (`hdeg_out`, `hdeg_pairs`): the polynomials in the oracle's handle
table have bounded `natDegree`. This file makes that fact structural: a `TableOp` inductive
mirroring the oracle's table-extension moves (SRS seed / linear combination / product), a
`buildTable` interpreter, and degree invariants proved by induction on the op list.

The bounds — each proved below, none assumed:

* `degree_invariant_linComb` — $B = D$ when no product op occurs. The seed powers $X^k$
  ($k \le D$) meet the bound exactly, and a linear combination degrades to the max of its
  operands' degrees (`Polynomial.natDegree_add_le` is a max-bound, `natDegree_C_mul_le` kills the
  scalar). This is the invariant behind `hdeg_out`: the committed output handle is a $G_1$ table
  entry.

* `degree_invariant` — $B = D \cdot 2^{\#\mathrm{mul}}$ for the flat table with products. A
  product's degree is bounded by the sum of its operands' (`Polynomial.natDegree_mul_le`), so each
  `mul` over a flat table can at worst double the running bound; the uniform flat bound is
  exponential in the product count, not $2 D$.

* `flat_2D_bound_false` — the naive "$B = 2 D$ once products are allowed" claim is false for the
  flat table, proved by nesting one product inside another (`[seed, mul, mul]` builds $X^4$ at
  $D = 1$).

* `degree_invariant_paired` — $B = 2 D$ is recovered in a separate pairing-disciplined peer model:
  a two-sorted table ($G_1$ / $G_t$) where products land in $G_t$ and hence never nest.
  `GgmAdaptive.Move` itself has no pairing constructor, so this peer is not an invariant for its
  operational run and is not used by the end-to-end theorem.

## References

* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
-/

open Polynomial

namespace GgmDegreeInvariant

variable {p : ℕ}

/-! ## The table operations and their interpreter -/

/-- A peer-model table-extension move: seeding with SRS powers, appending a linear combination,
or appending a formal product. Only the linear case mirrors `GgmAdaptive.runAux`; its actual
`Move` type has no product/pairing constructor. -/
inductive TableOp (p : ℕ) where
  /-- Append the SRS seed `1, X, …, X^D`. -/
  | seed : TableOp p
  /-- Append `a·table[i] + b·table[j]` (group op + scalar mul, as `GgmAdaptive.combine`). -/
  | linComb (i j : ℕ) (a b : ZMod p) : TableOp p
  /-- Append `table[i] * table[j]` (pairing product). -/
  | mul (i j : ℕ) : TableOp p

/-- The SRS seed table `[1, X, …, X^D]`. -/
noncomputable def srs (p D : ℕ) : List ((ZMod p)[X]) :=
  (List.range (D + 1)).map (fun k => X ^ k)

/-- One table-extension step. Out-of-range handles read the `0` polynomial, exactly as
`GgmAdaptive` does everywhere (`List.getD _ _ 0`). -/
noncomputable def applyOp (D : ℕ) (table : List ((ZMod p)[X])) :
    TableOp p → List ((ZMod p)[X])
  | .seed => table ++ srs p D
  | .linComb i j a b => table ++ [C a * table.getD i 0 + C b * table.getD j 0]
  | .mul i j => table ++ [table.getD i 0 * table.getD j 0]

/-- Build the handle table from an op list (head = last op applied), starting empty. -/
noncomputable def buildTable (D : ℕ) : List (TableOp p) → List ((ZMod p)[X])
  | [] => []
  | op :: ops => applyOp D (buildTable D ops) op

/-- The number of product ops in an op list — the doubling count of the flat bound. -/
def mulCount : List (TableOp p) → ℕ
  | [] => 0
  | .mul _ _ :: ops => mulCount ops + 1
  | .seed :: ops => mulCount ops
  | .linComb _ _ _ _ :: ops => mulCount ops

/-! ## Degree bookkeeping helpers -/

/-- A defaulted table read inherits any degree bound on the table (`0` has `natDegree 0`). -/
lemma natDegree_getD_le {table : List ((ZMod p)[X])} {B : ℕ}
    (h : ∀ q ∈ table, q.natDegree ≤ B) (i : ℕ) :
    (table.getD i 0).natDegree ≤ B := by
  by_cases hi : i < table.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    simp

/-- A binary linear combination of two bounded reads stays bounded: `natDegree_add_le` is a
MAX-bound and `natDegree_C_mul_le` absorbs the scalars: the linComb step preserves ANY bound. -/
lemma natDegree_linEntry_le {table : List ((ZMod p)[X])} {B : ℕ}
    (h : ∀ q ∈ table, q.natDegree ≤ B) (i j : ℕ) (a b : ZMod p) :
    (C a * table.getD i 0 + C b * table.getD j 0).natDegree ≤ B := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le a _).trans (natDegree_getD_le h i)
  · exact (natDegree_C_mul_le b _).trans (natDegree_getD_le h j)

/-- Every seed polynomial `X^k`, `k ≤ D`, has `natDegree ≤ D` (`natDegree_X_pow_le`; the
`≤` direction needs no nontriviality). -/
lemma natDegree_srs_le (D : ℕ) : ∀ q ∈ srs p D, q.natDegree ≤ D := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  exact (natDegree_X_pow_le k).trans (Nat.lt_succ_iff.mp (List.mem_range.mp hk))

/-! ## The flat-table invariants -/

/-- **The linComb-only degree invariant, B = D.** If the op list contains no product, every
table polynomial has `natDegree ≤ D` — by induction on the op list: the seed meets the bound
exactly and a linear combination degrades to the max of its operands. This is the structural
fact behind `GgmAdaptive`'s `hdeg_out` hypothesis (the committed output is a G₁ handle). -/
theorem degree_invariant_linComb (D : ℕ) (ops : List (TableOp p))
    (hops : mulCount ops = 0) :
    ∀ q ∈ buildTable D ops, q.natDegree ≤ D := by
  induction ops with
  | nil => intro q hq; simp [buildTable] at hq
  | cons op ops ih =>
    intro q hq
    cases op with
    | seed =>
      simp only [buildTable, applyOp] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih hops q h
      · exact natDegree_srs_le D q h
    | linComb i j a b =>
      simp only [buildTable, applyOp] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih hops q h
      · rw [List.mem_singleton.mp h]
        exact natDegree_linEntry_le (ih hops) i j a b
    | mul i j => simp [mulCount] at hops

/-- **The flat-table degree invariant with products: B = D · 2^(#mul).** By induction on the
op list: seed entries have degree ≤ D ≤ B, a linear combination keeps the running bound
(max), and a product at worst DOUBLES it (`natDegree_mul_le` is a SUM-bound), consuming one
`mul` from the count. Over a FLAT table this exponential bound is the honest one — a uniform
`2·D` is refuted below (`flat_2D_bound_false`); recovering `2·D` needs the pairing
discipline (`degree_invariant_paired`). -/
theorem degree_invariant (D : ℕ) (ops : List (TableOp p)) :
    ∀ q ∈ buildTable D ops, q.natDegree ≤ D * 2 ^ mulCount ops := by
  induction ops with
  | nil => intro q hq; simp [buildTable] at hq
  | cons op ops ih =>
    intro q hq
    have hDB : D ≤ D * 2 ^ mulCount ops :=
      le_mul_of_one_le_right (Nat.zero_le D) Nat.one_le_two_pow
    cases op with
    | seed =>
      simp only [buildTable, applyOp] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih q h
      · exact (natDegree_srs_le D q h).trans hDB
    | linComb i j a b =>
      simp only [buildTable, applyOp] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih q h
      · rw [List.mem_singleton.mp h]
        exact natDegree_linEntry_le ih i j a b
    | mul i j =>
      simp only [buildTable, applyOp] at hq
      have hstep : D * 2 ^ mulCount ops + D * 2 ^ mulCount ops
          = D * 2 ^ mulCount (.mul i j :: ops) := by
        show _ = D * 2 ^ (mulCount ops + 1)
        rw [pow_succ]; ring
      rcases List.mem_append.mp hq with h | h
      · exact (ih q h).trans (by rw [← hstep]; exact Nat.le_add_right _ _)
      · rw [List.mem_singleton.mp h]
        refine natDegree_mul_le.trans ?_
        rw [← hstep]
        exact Nat.add_le_add (natDegree_getD_le ih i) (natDegree_getD_le ih j)

/-- With at most ONE product op the flat bound specializes to `2·D` — the single honest
`2·D` statement available on the flat table. -/
theorem degree_invariant_one_mul (D : ℕ) (ops : List (TableOp p))
    (hops : mulCount ops ≤ 1) :
    ∀ q ∈ buildTable D ops, q.natDegree ≤ 2 * D := by
  intro q hq
  refine (degree_invariant D ops q hq).trans ?_
  calc D * 2 ^ mulCount ops
      ≤ D * 2 ^ 1 := Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by norm_num) hops)
    _ = 2 * D := by ring

/-- **The naive uniform `2·D` bound is FALSE on the flat table** (why `degree_invariant`
carries `2^(#mul)`): nesting one product inside another — `[seed, mul 1 1, mul 2 2]`, applied
seed-first — builds `X·X` and then `(X·X)·(X·X) = X^4` at `D = 1`, and `4 > 2·1`. Products
over a flat table COMPOUND; only the pairing discipline (below) forbids that. -/
theorem flat_2D_bound_false [Fact (Nat.Prime p)] :
    ∃ (D : ℕ) (ops : List (TableOp p)),
      ¬ ∀ q ∈ buildTable D ops, q.natDegree ≤ 2 * D := by
  refine ⟨1, [.mul 2 2, .mul 1 1, .seed], fun hall => ?_⟩
  have hsrs : srs p 1 = [X ^ 0, X ^ 1] := by
    simp [srs, List.range_succ]
  have htab : buildTable (p := p) 1 [.mul 2 2, .mul 1 1, .seed]
      = [X ^ 0, X ^ 1, X ^ 1 * X ^ 1, X ^ 1 * X ^ 1 * (X ^ 1 * X ^ 1)] := by
    simp only [buildTable, applyOp, hsrs, List.nil_append]
    norm_num [List.getD]
  have hmem : (X ^ 1 * X ^ 1 * (X ^ 1 * X ^ 1) : (ZMod p)[X])
      ∈ buildTable (p := p) 1 [.mul 2 2, .mul 1 1, .seed] := by
    rw [htab]; simp
  have hle := hall _ hmem
  have h4 : (X ^ 1 * X ^ 1 * (X ^ 1 * X ^ 1) : (ZMod p)[X]).natDegree = 4 := by
    have hX : (X ^ 1 * X ^ 1 * (X ^ 1 * X ^ 1) : (ZMod p)[X]) = X ^ 4 := by ring
    rw [hX, natDegree_X_pow]
  omega

/-! ## The pairing-disciplined invariant: B = 2·D, structurally

In this separate peer model, a product lands in Gₜ, out of which no further product is available.
Products therefore never nest. The two-sorted table below makes that discipline structural, and
the uniform bound `2·D` becomes an induction invariant. This section is not wired to
`GgmAdaptive.runAux`. -/

/-- A pairing-disciplined move: linear combinations within each sort, and a pairing product
whose operands are BOTH drawn from the G₁ table (degree ≤ D each — the faithful G₁ × G₂
version only lowers the Gₜ bound to D + 1) and whose result is appended to the Gₜ table. -/
inductive PairedOp (p : ℕ) where
  /-- Append `a·g1[i] + b·g1[j]` to the G₁ table. -/
  | linG1 (i j : ℕ) (a b : ZMod p) : PairedOp p
  /-- Append the pairing product `g1[i] * g1[j]` to the Gₜ table. -/
  | pair (i j : ℕ) : PairedOp p
  /-- Append `a·gt[i] + b·gt[j]` to the Gₜ table. -/
  | linGt (i j : ℕ) (a b : ZMod p) : PairedOp p

/-- Build the two-sorted `(G₁, Gₜ)` tables, seeding G₁ with the SRS. -/
noncomputable def buildPaired (D : ℕ) :
    List (PairedOp p) → List ((ZMod p)[X]) × List ((ZMod p)[X])
  | [] => (srs p D, [])
  | .linG1 i j a b :: ops =>
      ((buildPaired D ops).1
          ++ [C a * (buildPaired D ops).1.getD i 0 + C b * (buildPaired D ops).1.getD j 0],
        (buildPaired D ops).2)
  | .pair i j :: ops =>
      ((buildPaired D ops).1,
        (buildPaired D ops).2 ++ [(buildPaired D ops).1.getD i 0 * (buildPaired D ops).1.getD j 0])
  | .linGt i j a b :: ops =>
      ((buildPaired D ops).1,
        (buildPaired D ops).2
          ++ [C a * (buildPaired D ops).2.getD i 0 + C b * (buildPaired D ops).2.getD j 0])

/-- **The pairing-disciplined degree invariant.** By induction on the op list, jointly:
every G₁ entry has `natDegree ≤ D` (seed + max under linear combination) and every Gₜ entry
has `natDegree ≤ 2·D` (a pairing product SUMS two G₁ bounds — `natDegree_mul_le` — and Gₜ
linear combinations keep the max). No hypotheses: the bound the `GgmAdaptive` theorems
consume as `hdeg_out` / `hdeg_pairs` (via differences, `Δ = 2·D`) is structural here. -/
theorem degree_invariant_paired (D : ℕ) (ops : List (PairedOp p)) :
    (∀ q ∈ (buildPaired D ops).1, q.natDegree ≤ D) ∧
    (∀ q ∈ (buildPaired D ops).2, q.natDegree ≤ 2 * D) := by
  induction ops with
  | nil =>
    refine ⟨natDegree_srs_le D, ?_⟩
    intro q hq
    simp [buildPaired] at hq
  | cons op ops ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases op with
    | linG1 i j a b =>
      refine ⟨?_, ih2⟩
      intro q hq
      simp only [buildPaired] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih1 q h
      · rw [List.mem_singleton.mp h]
        exact natDegree_linEntry_le ih1 i j a b
    | pair i j =>
      refine ⟨ih1, ?_⟩
      intro q hq
      simp only [buildPaired] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih2 q h
      · rw [List.mem_singleton.mp h]
        refine natDegree_mul_le.trans ?_
        have h1 := natDegree_getD_le ih1 i
        have h2 := natDegree_getD_le ih1 j
        omega
    | linGt i j a b =>
      refine ⟨ih1, ?_⟩
      intro q hq
      simp only [buildPaired] at hq
      rcases List.mem_append.mp hq with h | h
      · exact ih2 q h
      · rw [List.mem_singleton.mp h]
        exact natDegree_linEntry_le ih2 i j a b

/-- **Uniform B = 2·D under the pairing discipline** — every handle of either sort. -/
theorem degree_invariant_paired_uniform (D : ℕ) (ops : List (PairedOp p)) :
    ∀ q ∈ (buildPaired D ops).1 ++ (buildPaired D ops).2, q.natDegree ≤ 2 * D := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact ((degree_invariant_paired D ops).1 q h).trans (by omega)
  · exact (degree_invariant_paired D ops).2 q h

end GgmDegreeInvariant
