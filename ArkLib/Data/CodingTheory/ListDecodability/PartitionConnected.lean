/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability
public import ArkLib.ToMathlib.Combinatorics.Hypergraph.PartitionConnected

/-!
# Large lists give weakly partition-connected agreement hypergraphs

For a received word `y : ι → A` and a family of words `c : V → ι → A`, the agreement hypergraph
has vertex set `V` and one edge per coordinate, `fun i ↦ {j | c j i = y i}`: the words that agree
with `y` at `i`. If the distances from `y` to the words sum to at most `(card V - 1) * (n - κ)`,
where `n = card ι`, the edges carry total weight `∑ i, (#{j | c j i = y i} - 1)` at least
`κ * (card V - 1)`, so by `exists_isWeaklyPartitionConnected_subtype` the agreement hypergraph of
some subfamily indexed by at least two elements of `V` is `κ`-weakly partition-connected.

For a code `C`, a list of more than `ℓ` codewords around one word at relative radius
`ℓ / (ℓ + 1) * (1 - κ / n)` is such a family. Nothing is assumed about the code, and of the
alphabet only decidable equality.

## Main statements

* `Code.exists_isWeaklyPartitionConnected_agreement_of_sum_hammingDist_le`: if
  `∑ j, Δ₀(y, c j) ≤ (card V - 1) * (n - κ)` and `V` has at least two elements, the agreement
  hypergraph of `y` and the words `c j` with `j ∈ S` is `κ`-weakly partition-connected for some
  `S` with `2 ≤ #S`.
* `Code.exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda`: if `0 < ℓ` and
  `ℓ < Lambda C (ℓ / (ℓ + 1) * (1 - κ / n))`, there are a word `y`, a number `s` with
  `1 ≤ s ≤ ℓ`, and `s + 1` distinct codewords in the point list of `C` around `y` at that radius
  whose agreement hypergraph is `κ`-weakly partition-connected.

The first is the lemma of [AGL24] that a bad list-decoding configuration gives a weakly
partition-connected agreement hypergraph, with a real parameter `κ` in place of their positive
integer `k`; the second is the form in which it is applied to list sizes.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

open Finset

namespace Code

variable {ι A : Type*} [Fintype ι] [DecidableEq A]

/-- Summed over the coordinates, the agreement hypergraph of `y` and `c` has weight at least the
total agreement of the words `c j` with `y`, less the number of coordinates. -/
private theorem sum_agree_le_sum_card_filter_sub_one_add {V : Type*} [Fintype V] (y : ι → A)
    (c : V → ι → A) :
    ∑ j, agree (c j) y ≤ ∑ i, (#{j | c j i = y i} - 1) + Fintype.card ι := by
  calc ∑ j, agree (c j) y = ∑ i, #{j | c j i = y i} := by
        simp only [agree, card_filter]
        exact sum_comm
    _ ≤ ∑ i, (#{j | c j i = y i} - 1 + 1) := sum_le_sum fun i _ ↦ by omega
    _ = _ := by rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]

/-- If the distances from `y` to the words `c j` sum to at most `(card V - 1) * (n - κ)`, the
agreement hypergraph has weight at least `κ * (card V - 1)`. -/
private theorem le_sum_card_filter_sub_one_of_sum_hammingDist_le {V : Type*} [Fintype V]
    {y : ι → A} {c : V → ι → A} {κ : ℝ} (hV : 1 ≤ Fintype.card V)
    (hdist : (∑ j, (Δ₀(y, c j) : ℝ)) ≤ (Fintype.card V - 1 : ℝ) * (Fintype.card ι - κ)) :
    κ * ((Fintype.card V - 1 : ℕ) : ℝ) ≤ ((∑ i, (#{j | c j i = y i} - 1) : ℕ) : ℝ) := by
  have hagree (j : V) : (agree (c j) y : ℝ) = Fintype.card ι - Δ₀(y, c j) := by
    rw [eq_sub_iff_add_eq, hammingDist_comm]
    exact_mod_cast agree_add_hammingDist
  have hsum : ((∑ j, agree (c j) y : ℕ) : ℝ) ≤
      ((∑ i, (#{j | c j i = y i} - 1) : ℕ) : ℝ) + Fintype.card ι := by
    exact_mod_cast sum_agree_le_sum_card_filter_sub_one_add y c
  rw [Nat.cast_sum, sum_congr rfl fun j _ ↦ hagree j, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul] at hsum
  rw [Nat.cast_sub hV, Nat.cast_one]
  linarith

/-- **A close family has a weakly partition-connected agreement hypergraph** ([AGL24]). If `V`
has at least two elements and the distances from `y` to the words `c j` sum to at most
`(card V - 1) * (n - κ)`, then for some `S` with `2 ≤ #S` the agreement hypergraph of `y` and the
words `c j`, `j ∈ S`, is `κ`-weakly partition-connected. -/
theorem exists_isWeaklyPartitionConnected_agreement_of_sum_hammingDist_le {V : Type*}
    [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) {y : ι → A} {c : V → ι → A} {κ : ℝ}
    (hdist : (∑ j, (Δ₀(y, c j) : ℝ)) ≤ (Fintype.card V - 1 : ℝ) * (Fintype.card ι - κ)) :
    ∃ S : Finset V, 2 ≤ #S ∧
      IsWeaklyPartitionConnected (fun i ↦ {j : S | c j i = y i}) κ := by
  obtain ⟨S, hS, hwpc⟩ := exists_isWeaklyPartitionConnected_subtype hV
    (le_sum_card_filter_sub_one_of_sum_hammingDist_le (by omega) hdist)
  refine ⟨S, hS, ?_⟩
  convert hwpc using 2 with i
  ext j
  simp

/-- A word in the point list at radius `ℓ / (ℓ + 1) * (1 - κ / n)` is at distance at most
`ℓ / (ℓ + 1) * (n - κ)`. -/
private theorem hammingDist_le_of_mem_closeCodewordsRel {C : Set (ι → A)} {y c : ι → A}
    {ℓ : ℕ} {κ : ℝ} (hn : 0 < Fintype.card ι)
    (hc : c ∈ closeCodewordsRel C y ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / Fintype.card ι))) :
    (Δ₀(y, c) : ℝ) ≤ (ℓ : ℝ) / (ℓ + 1) * (Fintype.card ι - κ) := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := (mem_closeCodewordsRel_iff.1 hc).2
  rwa [relHammingDist_coe, div_le_iff₀ hnR, mul_assoc, sub_mul, one_mul,
    div_mul_cancel₀ _ hnR.ne'] at h

/-- A set with more than `ℓ` elements contains `ℓ + 1` distinct elements. -/
private theorem exists_embedding_of_lt_encard {α : Type*} {s : Set α} {ℓ : ℕ}
    (h : (ℓ : ℕ∞) < s.encard) : ∃ c : Fin (ℓ + 1) ↪ α, ∀ j, c j ∈ s := by
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt h)
  have hfin : t.Finite := Set.finite_of_encard_eq_coe (k := ℓ + 1) (by rw [ht]; norm_cast)
  have hcard : #hfin.toFinset = ℓ + 1 := by
    have := hfin.encard_eq_coe_toFinset_card
    rw [ht] at this
    exact_mod_cast this.symm
  exact ⟨(finCongr hcard.symm).toEmbedding.trans
    (hfin.toFinset.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)),
    fun j ↦ hts (hfin.mem_toFinset.1 (Subtype.prop _))⟩

/-- **Large lists give weakly partition-connected agreement hypergraphs.** If `0 < ℓ` and
`Lambda C (ℓ / (ℓ + 1) * (1 - κ / n)) > ℓ`, then there are a word `y`, a number `s` with
`1 ≤ s ≤ ℓ`, and `s + 1` distinct codewords of `C` within that relative radius of `y` whose
agreement hypergraph `fun i ↦ {j | c j i = y i}` is `κ`-weakly partition-connected. -/
theorem exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda {C : Set (ι → A)} {ℓ : ℕ}
    (hℓ : 0 < ℓ) {κ : ℝ}
    (h : (ℓ : ℕ∞) < Lambda C ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / Fintype.card ι))) :
    ∃ y : ι → A, ∃ s : ℕ, 1 ≤ s ∧ s ≤ ℓ ∧ ∃ c : Fin (s + 1) ↪ (ι → A),
      (∀ j, c j ∈ closeCodewordsRel C y ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / Fintype.card ι))) ∧
      IsWeaklyPartitionConnected (fun i ↦ {j | c j i = y i}) κ := by
  set δ : ℝ := (ℓ : ℝ) / (ℓ + 1) * (1 - κ / Fintype.card ι)
  obtain ⟨y, hy⟩ : ∃ y, (ℓ : ℕ∞) < (closeCodewordsRel C y δ).encard := by
    by_contra hcon
    exact h.not_ge (Lambda_le_iff_forall_encard_le.2 fun y ↦ not_lt.1 fun hy ↦ hcon ⟨y, hy⟩)
  obtain ⟨c, hc⟩ := exists_embedding_of_lt_encard hy
  have hn : 0 < Fintype.card ι := by
    have h0 : (0 : Fin (ℓ + 1)) ≠ Fin.last ℓ := Fin.ext_iff.not.2 (by simpa using hℓ.ne)
    obtain ⟨i, -⟩ := Function.ne_iff.1 (c.injective.ne h0)
    exact Fintype.card_pos_iff.2 ⟨i⟩
  have hdist : (∑ j, (Δ₀(y, c j) : ℝ)) ≤
      (Fintype.card (Fin (ℓ + 1)) - 1 : ℝ) * (Fintype.card ι - κ) := by
    have hsum := sum_le_sum fun j (_ : j ∈ univ) ↦
      hammingDist_le_of_mem_closeCodewordsRel hn (hc j)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact hsum.trans_eq (by field_simp)
  obtain ⟨S, hS, hwpc⟩ := exists_isWeaklyPartitionConnected_agreement_of_sum_hammingDist_le
    (by rw [Fintype.card_fin]; omega) hdist
  have hS' : #S - 1 + 1 = #S := by omega
  let e : S ≃ Fin (#S - 1 + 1) := S.equivFin.trans (finCongr hS'.symm)
  refine ⟨y, #S - 1, by omega, ?_,
    (e.symm.toEmbedding.trans (Function.Embedding.subtype _)).trans c, fun j ↦ hc _, ?_⟩
  · have := (card_le_univ S).trans_eq (Fintype.card_fin _)
    omega
  · rw [← isWeaklyPartitionConnected_map_equiv e] at hwpc
    convert hwpc using 2 with i
    ext j
    simp [mem_map_equiv]

end Code
