/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Weakly partition-connected hypergraphs

A hypergraph with vertices in a finite type `V` and edges indexed by a finite type `ι` is a family
`H : ι → Finset V`; edges may repeat and may be empty. For `κ : ℝ`, `H` is `κ`-weakly
partition-connected if every finpartition `P` of `univ` satisfies
`κ * (#P.parts - 1) ≤ ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1)`:
summed over the edges, the number of parts an edge meets beyond its first is at least `κ` for every
part beyond the first. Both subtractions are truncated in `ℕ`, so an empty edge contributes `0`.
This is the weak partition-connectivity of [AGL24], with a real parameter `κ` in place of their
positive integer `k`. With no vertices every `H` is `κ`-weakly partition-connected.

## Main definitions

* `IsWeaklyPartitionConnected H κ`: the condition above.

## Main statements

* `IsWeaklyPartitionConnected.mono`: the condition is antitone in `κ`.
* `IsWeaklyPartitionConnected.of_add`, `IsWeaklyPartitionConnected.delete`: changing at most `b`
  edges arbitrarily (in particular emptying them) costs at most `b` in `κ`.
* `IsWeaklyPartitionConnected.le_card_filter_inter_nonempty`,
  `IsWeaklyPartitionConnected.le_card_filter_mem`: with at least two vertices, at least `κ` edges
  meet every nonempty vertex set; in particular every vertex has degree at least `κ`.
* `isWeaklyPartitionConnected_congr_of_card_le_one`,
  `isWeaklyPartitionConnected_restrict_edges_iff`:
  edges with at most one vertex do not matter.
* `isWeaklyPartitionConnected_comp_equiv`, `isWeaklyPartitionConnected_map_equiv`: invariance
  under relabelling edges and vertices.
* `isWeaklyPartitionConnected_natCast_iff`: for `κ = k : ℕ`, the condition says that
  `A ↦ #{i | (H i ∩ A).Nonempty} - k` does not decrease when summed over the parts of a
  finpartition, starting from `univ`.
* `isWeaklyPartitionConnected_of_forall_ssubset`, `exists_isWeaklyPartitionConnected_subtype`: if
  `∑ i, (#(H i) - 1) ≥ κ * (card V - 1)` and no proper vertex set `U` with `2 ≤ #U` has
  `∑ i, (#(H i ∩ U) - 1) > κ * (#U - 1)`, then `H` is `κ`-weakly partition-connected; hence such
  an `H` on at least two vertices induces a `κ`-weakly partition-connected hypergraph on some
  vertex set with at least two elements.
* `IsWeaklyPartitionConnected.le_sum_card_sub_one`: conversely, a `κ`-weakly partition-connected
  `H` has `∑ i, (#(H i) - 1) ≥ κ * (card V - 1)`.
* `Finpartition.card_filter_inter_nonempty_le`, `Finpartition.sum_card_inter`: a finset meets at
  most `#e` parts, and its intersections with the parts partition it.

`exists_isWeaklyPartitionConnected_subtype` is the lemma of [AGL24] that a hypergraph on at least
two vertices of total weight at least `k * (card V - 1)` induces a `k`-weakly partition-connected
hypergraph on some set of at least two vertices; `IsWeaklyPartitionConnected.delete` is the
combinatorial step of their robustness-to-deletions lemma.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

open Finset

namespace Finpartition

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-- A finset meets at most as many parts of a finpartition as it has elements. -/
theorem card_filter_inter_nonempty_le (P : Finpartition s) (e : Finset V) :
    #{A ∈ P.parts | (e ∩ A).Nonempty} ≤ #e := by
  refine (card_le_card (t := e.image P.part) fun A hA ↦ ?_).trans card_image_le
  obtain ⟨hA, v, hv⟩ := mem_filter.1 hA
  rw [mem_inter] at hv
  exact mem_image.2 ⟨v, hv.1, P.part_eq_of_mem hA hv.2⟩

/-- A finset contained in `s` has as many elements as its intersections with the parts. -/
theorem sum_card_inter (P : Finpartition s) {e : Finset V} (he : e ⊆ s) :
    ∑ A ∈ P.parts, #(e ∩ A) = #e := by
  rw [← (P.restrict he).sum_card_parts, P.sum_restrict he card card_empty]
  exact sum_congr rfl fun A _ ↦ by rw [inter_comm]

end Finpartition

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]

/-- A family of finsets `H : ι → Finset V`, read as a hypergraph with vertices `V` and edges
`H i`, is `κ`-weakly partition-connected if for every finpartition `P` of `univ`, `κ` times the
number of parts beyond the first is at most the sum over the edges of the number of parts the edge
meets beyond its first. Subtractions are in `ℕ`. With no vertices every `H` is `κ`-weakly
partition-connected. -/
def IsWeaklyPartitionConnected (H : ι → Finset V) (κ : ℝ) : Prop :=
  ∀ P : Finpartition (univ : Finset V),
    κ * ((#P.parts - 1 : ℕ) : ℝ) ≤ ((∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) : ℕ) : ℝ)

variable {H H' : ι → Finset V} {κ κ' b : ℝ}

/-- A nonempty finset meets some part of a finpartition of `univ`. -/
private theorem nonempty_filter_inter_nonempty (P : Finpartition (univ : Finset V))
    {e : Finset V} (he : e.Nonempty) : ({A ∈ P.parts | (e ∩ A).Nonempty}).Nonempty := by
  obtain ⟨v, hv⟩ := he
  exact ⟨P.part v, mem_filter.2 ⟨P.part_mem.2 (mem_univ v),
    v, mem_inter.2 ⟨hv, P.mem_part_self.2 (mem_univ v)⟩⟩⟩

/-- For one edge `e`, the parts it meets beyond its first plus its elements beyond the first in
each part are its elements beyond its first. -/
private theorem card_filter_sub_one_add_sum (P : Finpartition (univ : Finset V))
    (e : Finset V) :
    #{A ∈ P.parts | (e ∩ A).Nonempty} - 1 + ∑ A ∈ P.parts, (#(e ∩ A) - 1) = #e - 1 := by
  have h : ∑ A ∈ P.parts, (#(e ∩ A) - 1) + #{A ∈ P.parts | (e ∩ A).Nonempty} = #e := by
    rw [card_filter, ← sum_add_distrib, ← P.sum_card_inter (subset_univ e)]
    refine sum_congr rfl fun A _ ↦ ?_
    split_ifs with hA
    · have := hA.card_pos
      omega
    · rw [not_nonempty_iff_eq_empty.1 hA]
      simp
  rcases e.eq_empty_or_nonempty with rfl | he
  · simp
  · have := (nonempty_filter_inter_nonempty P he).card_pos
    omega

/-- The weight identity: summed over the edges, the parts met beyond the first plus the elements
beyond the first inside each part give the elements beyond the first. -/
private theorem sum_card_filter_sub_one_add_sum (H : ι → Finset V)
    (P : Finpartition (univ : Finset V)) :
    ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) + ∑ A ∈ P.parts, ∑ i, (#(H i ∩ A) - 1) =
      ∑ i, (#(H i) - 1) := by
  rw [sum_comm (s := P.parts), ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ card_filter_sub_one_add_sum P (H i)

/-- Weak partition-connectivity is antitone in `κ`. -/
theorem IsWeaklyPartitionConnected.mono (h : IsWeaklyPartitionConnected H κ') (hκ : κ ≤ κ') :
    IsWeaklyPartitionConnected H κ :=
  fun P ↦ (mul_le_mul_of_nonneg_right hκ (Nat.cast_nonneg _)).trans (h P)

/-- If `H` is `(κ + b)`-weakly partition-connected and `H'` contains `H` outside a set `B` of at
most `b` edges, then `H'` is `κ`-weakly partition-connected. -/
theorem IsWeaklyPartitionConnected.of_add {B : Finset ι}
    (h : IsWeaklyPartitionConnected H (κ + b)) (hB : (#B : ℝ) ≤ b)
    (hH : ∀ i ∉ B, H i ⊆ H' i) : IsWeaklyPartitionConnected H' κ := by
  classical
  intro P
  have hle : ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) ≤
      ∑ i, (#{A ∈ P.parts | (H' i ∩ A).Nonempty} - 1) + #B * (#P.parts - 1) := by
    calc _ ≤ ∑ i, ((#{A ∈ P.parts | (H' i ∩ A).Nonempty} - 1) +
          if i ∈ B then #P.parts - 1 else 0) := sum_le_sum fun i _ ↦ ?_
      _ = _ := by rw [sum_add_distrib, sum_ite_mem, univ_inter, sum_const, smul_eq_mul]
    split_ifs with hi
    · exact (Nat.sub_le_sub_right (card_le_card (filter_subset _ _)) 1).trans
        (Nat.le_add_left _ _)
    · refine Nat.sub_le_sub_right (card_le_card fun A hA ↦ ?_) 1
      rw [mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.mono (inter_subset_inter (hH i hi) subset_rfl)⟩
  have hle' : ((∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) : ℕ) : ℝ) ≤
      ((∑ i, (#{A ∈ P.parts | (H' i ∩ A).Nonempty} - 1) : ℕ) : ℝ) +
        (#B : ℝ) * ((#P.parts - 1 : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hBm := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg (α := ℝ) (#P.parts - 1))
  linarith [h P]

/-- Emptying a set of at most `b` edges of a `(κ + b)`-weakly partition-connected hypergraph
leaves a `κ`-weakly partition-connected hypergraph. -/
theorem IsWeaklyPartitionConnected.delete [DecidableEq ι] {B : Finset ι}
    (h : IsWeaklyPartitionConnected H (κ + b)) (hB : (#B : ℝ) ≤ b) :
    IsWeaklyPartitionConnected (fun i ↦ if i ∈ B then ∅ else H i) κ :=
  h.of_add hB fun i hi ↦ by simp [hi]

/-- A `κ`-weakly partition-connected hypergraph has weight `∑ i, (#(H i) - 1)` at least
`κ * (card V - 1)`. -/
theorem IsWeaklyPartitionConnected.le_sum_card_sub_one (h : IsWeaklyPartitionConnected H κ) :
    κ * ((Fintype.card V - 1 : ℕ) : ℝ) ≤ ((∑ i, (#(H i) - 1) : ℕ) : ℝ) := by
  have hz : ∑ A ∈ (⊥ : Finpartition (univ : Finset V)).parts, ∑ i, (#(H i ∩ A) - 1) = 0 :=
    sum_eq_zero fun A hA ↦ sum_eq_zero fun i _ ↦ by
      obtain ⟨v, -, rfl⟩ := Finpartition.mem_bot_iff.1 hA
      have := card_le_card (inter_subset_right (s₁ := H i) (s₂ := {v}))
      rw [card_singleton] at this
      omega
  have hid := sum_card_filter_sub_one_add_sum H ⊥
  rw [hz, add_zero] at hid
  have h' := h ⊥
  rwa [Finpartition.card_bot, card_univ, hid] at h'

/-- At least `κ` edges meet a nonempty proper vertex set. -/
private theorem IsWeaklyPartitionConnected.le_card_filter_inter_nonempty_of_ne_univ
    (h : IsWeaklyPartitionConnected H κ) {A : Finset V} (hA : A.Nonempty) (hA' : A ≠ univ) :
    κ ≤ #{i | (H i ∩ A).Nonempty} := by
  have hAc : Aᶜ ≠ ⊥ := by rwa [Ne, bot_eq_empty, compl_eq_empty_iff]
  let P : Finpartition (univ : Finset V) := (Finpartition.indiscrete hA.ne_empty).extend hAc
    disjoint_compl_right (by rw [sup_compl_eq_top, top_eq_univ])
  have hP : P.parts = {Aᶜ, A} := rfl
  have hne : Aᶜ ≠ A := fun hc ↦ by
    obtain ⟨v, hv⟩ := hA
    have hv' : v ∈ Aᶜ := by rw [hc]; exact hv
    exact mem_compl.1 hv' hv
  have h2 := h P
  rw [hP, card_pair hne, show (2 - 1 : ℕ) = 1 from rfl, Nat.cast_one, mul_one] at h2
  refine h2.trans (Nat.cast_le.2 ?_)
  rw [card_filter]
  refine sum_le_sum fun i _ ↦ ?_
  split_ifs with hi
  · have h1 := card_le_card (filter_subset (fun B ↦ (H i ∩ B).Nonempty) {Aᶜ, A})
    have h3 := card_insert_le Aᶜ ({A} : Finset (Finset V))
    rw [card_singleton] at h3
    omega
  · have h1 : #{B ∈ ({Aᶜ, A} : Finset (Finset V)) | (H i ∩ B).Nonempty} ≤ 1 := by
      refine (card_le_card fun B hB ↦ ?_).trans (card_singleton Aᶜ).le
      rw [mem_filter, mem_insert, mem_singleton] at hB
      rcases hB with ⟨rfl | rfl, hB⟩
      · exact mem_singleton_self _
      · exact absurd hB hi
    omega

/-- In a `κ`-weakly partition-connected hypergraph with at least two vertices, at least `κ` edges
meet every nonempty vertex set. -/
theorem IsWeaklyPartitionConnected.le_card_filter_inter_nonempty [Nontrivial V]
    (h : IsWeaklyPartitionConnected H κ) {A : Finset V} (hA : A.Nonempty) :
    κ ≤ #{i | (H i ∩ A).Nonempty} := by
  by_cases hA' : A = univ
  · obtain ⟨v, w, hvw⟩ := exists_pair_ne V
    refine (h.le_card_filter_inter_nonempty_of_ne_univ (singleton_nonempty v)
      fun hv ↦ hvw (mem_singleton.1 (hv ▸ mem_univ w)).symm).trans
      (Nat.cast_le.2 (card_le_card fun i hi ↦ ?_))
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.mono (inter_subset_inter subset_rfl (hA' ▸ subset_univ _))⟩
  · exact h.le_card_filter_inter_nonempty_of_ne_univ hA hA'

/-- In a `κ`-weakly partition-connected hypergraph with at least two vertices, every vertex lies
in at least `κ` edges. -/
theorem IsWeaklyPartitionConnected.le_card_filter_mem [Nontrivial V]
    (h : IsWeaklyPartitionConnected H κ) (v : V) : κ ≤ #{i | v ∈ H i} := by
  have hv (i : ι) : (H i ∩ {v}).Nonempty ↔ v ∈ H i :=
    ⟨fun ⟨w, hw⟩ ↦ by
      rw [mem_inter, mem_singleton] at hw
      exact hw.2 ▸ hw.1,
    fun hv ↦ ⟨v, mem_inter.2 ⟨hv, mem_singleton_self v⟩⟩⟩
  simpa only [hv] using h.le_card_filter_inter_nonempty (singleton_nonempty v)

/-- Changing edges that have at most one vertex before and after does not affect weak
partition-connectivity. -/
theorem isWeaklyPartitionConnected_congr_of_card_le_one
    (hH : ∀ i, H i = H' i ∨ #(H i) ≤ 1 ∧ #(H' i) ≤ 1) :
    IsWeaklyPartitionConnected H κ ↔ IsWeaklyPartitionConnected H' κ := by
  have hsum (P : Finpartition (univ : Finset V)) :
      ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) =
        ∑ i, (#{A ∈ P.parts | (H' i ∩ A).Nonempty} - 1) := by
    refine sum_congr rfl fun i _ ↦ ?_
    rcases hH i with h | ⟨h, h'⟩
    · rw [h]
    · have := (P.card_filter_inter_nonempty_le (H i)).trans h
      have := (P.card_filter_inter_nonempty_le (H' i)).trans h'
      omega
  simp only [IsWeaklyPartitionConnected, hsum]

/-- Dropping edges with at most one vertex does not affect weak partition-connectivity. -/
theorem isWeaklyPartitionConnected_restrict_edges_iff {p : ι → Prop} [DecidablePred p]
    (hp : ∀ i, ¬p i → #(H i) ≤ 1) :
    IsWeaklyPartitionConnected (fun i : Subtype p ↦ H i) κ ↔ IsWeaklyPartitionConnected H κ := by
  refine forall_congr' fun P ↦ ?_
  have hsum : ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) =
      ∑ i : Subtype p, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p, Fintype.sum_eq_zero
      (fun i : {i // ¬p i} ↦ #{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) fun i ↦ ?_, add_zero]
    have := (P.card_filter_inter_nonempty_le (H i)).trans (hp i i.2)
    omega
  rw [hsum]

/-- Relabelling the edges does not affect weak partition-connectivity. -/
theorem isWeaklyPartitionConnected_comp_equiv {ι' : Type*} [Fintype ι'] (e : ι' ≃ ι) :
    IsWeaklyPartitionConnected (H ∘ e) κ ↔ IsWeaklyPartitionConnected H κ := by
  refine forall_congr' fun P ↦ ?_
  rw [Function.comp_def, e.sum_comp fun i ↦ #{A ∈ P.parts | (H i ∩ A).Nonempty} - 1]

/-- One direction of `isWeaklyPartitionConnected_map_equiv`. -/
private theorem IsWeaklyPartitionConnected.of_map_equiv {W : Type*} [Fintype W] [DecidableEq W]
    (e : V ≃ W) {H' : ι → Finset W} (hH : ∀ i, H' i = (H i).map e.toEmbedding)
    (h : IsWeaklyPartitionConnected H κ) : IsWeaklyPartitionConnected H' κ := by
  intro P
  let eo : Finset W ≃o Finset V :=
    { e.symm.finsetCongr with map_rel_iff' := map_subset_map }
  have hparts : ((P.map eo).copy (map_univ_equiv e.symm)).parts =
      P.parts.map eo.toEquiv.toEmbedding := rfl
  have hfilter (i : ι) :
      #{A ∈ ((P.map eo).copy (map_univ_equiv e.symm)).parts | (H i ∩ A).Nonempty} =
        #{B ∈ P.parts | (H' i ∩ B).Nonempty} := by
    rw [hparts, filter_map, card_map]
    refine congrArg card (filter_congr fun B _ ↦ ?_)
    rw [hH i, Function.comp_apply]
    constructor
    · rintro ⟨v, hv⟩
      rw [mem_inter] at hv
      have hvB : v ∈ B.map e.symm.toEmbedding := hv.2
      rw [mem_map_equiv] at hvB
      exact ⟨e v, mem_inter.2 ⟨mem_map_of_mem _ hv.1, hvB⟩⟩
    · rintro ⟨w, hw⟩
      rw [mem_inter, mem_map_equiv] at hw
      have hwB : e.symm w ∈ B.map e.symm.toEmbedding := mem_map_equiv.2 (by simpa using hw.2)
      exact ⟨e.symm w, mem_inter.2 ⟨hw.1, hwB⟩⟩
  have hS : ∑ i, (#{A ∈ ((P.map eo).copy (map_univ_equiv e.symm)).parts |
      (H i ∩ A).Nonempty} - 1) = ∑ i, (#{B ∈ P.parts | (H' i ∩ B).Nonempty} - 1) :=
    sum_congr rfl fun i _ ↦ by rw [hfilter i]
  have h' := h ((P.map eo).copy (map_univ_equiv e.symm))
  rwa [hS, hparts, card_map] at h'

/-- Relabelling the vertices along an equivalence does not affect weak partition-connectivity. -/
theorem isWeaklyPartitionConnected_map_equiv {W : Type*} [Fintype W] [DecidableEq W]
    (e : V ≃ W) :
    IsWeaklyPartitionConnected (fun i ↦ (H i).map e.toEmbedding) κ ↔
      IsWeaklyPartitionConnected H κ :=
  ⟨fun h ↦ h.of_map_equiv e.symm fun i ↦ by ext; simp [mem_map_equiv],
    fun h ↦ h.of_map_equiv e fun _ ↦ rfl⟩

/-- For one edge `e`, the parts it meets beyond its first, plus one if `e` is nonempty, are the
parts it meets. -/
private theorem card_filter_sub_one_add_ite (P : Finpartition (univ : Finset V))
    (e : Finset V) :
    #{A ∈ P.parts | (e ∩ A).Nonempty} - 1 + (if e.Nonempty then 1 else 0) =
      #{A ∈ P.parts | (e ∩ A).Nonempty} := by
  split_ifs with he
  · exact Nat.sub_add_cancel (nonempty_filter_inter_nonempty P he).card_pos
  · rw [not_nonempty_iff_eq_empty.1 he]
    simp

/-- For a natural number `k`, `H` is `k`-weakly partition-connected if and only if
`g A = #{i | (H i ∩ A).Nonempty} - k` satisfies `g univ ≤ ∑ A ∈ P.parts, g A` for every
finpartition `P` of `univ`. -/
theorem isWeaklyPartitionConnected_natCast_iff (H : ι → Finset V) (k : ℕ) :
    IsWeaklyPartitionConnected H k ↔ ∀ P : Finpartition (univ : Finset V),
      (#{i | (H i).Nonempty} : ℤ) - k ≤
        ∑ A ∈ P.parts, ((#{i | (H i ∩ A).Nonempty} : ℤ) - k) := by
  refine forall_congr' fun P ↦ ?_
  have hST : ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) + #{i | (H i).Nonempty} =
      ∑ A ∈ P.parts, #{i | (H i ∩ A).Nonempty} := by
    calc _ = ∑ i, #{A ∈ P.parts | (H i ∩ A).Nonempty} := by
          rw [card_filter (fun i ↦ (H i).Nonempty), ← sum_add_distrib]
          exact sum_congr rfl fun i _ ↦ card_filter_sub_one_add_ite P (H i)
      _ = _ := by
          simp only [card_filter]
          exact sum_comm
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← Nat.cast_sum, ← hST]
  generalize ∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) = S
  generalize #{i | (H i).Nonempty} = N
  generalize #P.parts = p
  rcases p with _ | m
  · exact iff_of_true (by simp) (by push_cast; omega)
  · rw [Nat.add_sub_cancel]
    push_cast
    constructor
    · intro h
      have : ((k * m : ℕ) : ℤ) ≤ S := by exact_mod_cast h
      push_cast at this
      linarith
    · intro h
      have : ((k * m : ℕ) : ℤ) ≤ S := by push_cast; linarith
      exact_mod_cast this

/-- If `H` is heavy, `κ * (card V - 1) ≤ ∑ i, (#(H i) - 1)`, and no proper vertex set `U` with
`2 ≤ #U` is heavier, `∑ i, (#(H i ∩ U) - 1) ≤ κ * (#U - 1)`, then `H` is `κ`-weakly
partition-connected. -/
theorem isWeaklyPartitionConnected_of_forall_ssubset
    (hheavy : κ * ((Fintype.card V - 1 : ℕ) : ℝ) ≤ ((∑ i, (#(H i) - 1) : ℕ) : ℝ))
    (hmin : ∀ U : Finset V, U ⊂ univ → 2 ≤ #U →
      ((∑ i, (#(H i ∩ U) - 1) : ℕ) : ℝ) ≤ κ * ((#U - 1 : ℕ) : ℝ)) :
    IsWeaklyPartitionConnected H κ := by
  intro P
  rcases le_or_gt #P.parts 1 with hP | hP
  · rw [Nat.sub_eq_zero_of_le hP, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  have hpart (A : Finset V) (hA : A ∈ P.parts) :
      ((∑ i, (#(H i ∩ A) - 1) : ℕ) : ℝ) ≤ κ * ((#A - 1 : ℕ) : ℝ) := by
    rcases le_or_gt #A 1 with hA1 | hA1
    · rw [Nat.sub_eq_zero_of_le hA1, sum_eq_zero fun i _ ↦
        Nat.sub_eq_zero_of_le ((card_le_card inter_subset_right).trans hA1)]
      simp
    · refine hmin A ⟨subset_univ A, fun hsub ↦ ?_⟩ hA1
      obtain ⟨B, hB, hBA⟩ := exists_mem_ne hP A
      obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hB
      exact hBA (P.eq_of_mem_parts hB hA hv (hsub (mem_univ v)))
  have hsum : ((∑ A ∈ P.parts, ∑ i, (#(H i ∩ A) - 1) : ℕ) : ℝ) ≤
      κ * ((∑ A ∈ P.parts, (#A - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sum, Nat.cast_sum, mul_sum]
    exact sum_le_sum hpart
  have hparts : ∑ A ∈ P.parts, (#A - 1) + #P.parts = Fintype.card V := by
    rw [← card_univ, ← P.sum_card_parts, card_eq_sum_ones P.parts, ← sum_add_distrib]
    exact sum_congr rfl fun A hA ↦ Nat.sub_add_cancel (P.nonempty_of_mem_parts hA).card_pos
  have hid : ((∑ i, (#{A ∈ P.parts | (H i ∩ A).Nonempty} - 1) : ℕ) : ℝ) +
      ((∑ A ∈ P.parts, ∑ i, (#(H i ∩ A) - 1) : ℕ) : ℝ) = ((∑ i, (#(H i) - 1) : ℕ) : ℝ) := by
    rw [← Nat.cast_add, sum_card_filter_sub_one_add_sum]
  have hparts' : ((∑ A ∈ P.parts, (#A - 1) : ℕ) : ℝ) =
      (Fintype.card V : ℝ) - (#P.parts : ℝ) := by
    rw [← hparts, Nat.cast_add]
    ring
  have hV : 1 ≤ Fintype.card V := by omega
  rw [Nat.cast_sub hV, Nat.cast_one] at hheavy
  rw [Nat.cast_sub hP.le, Nat.cast_one]
  rw [hparts'] at hsum
  linarith

/-- If a hypergraph on at least two vertices satisfies `κ * (card V - 1) ≤ ∑ i, (#(H i) - 1)`,
then some vertex set `S` with `2 ≤ #S` induces a `κ`-weakly partition-connected hypergraph, with
edges `H i ∩ S`. -/
theorem exists_isWeaklyPartitionConnected_subtype (hV : 2 ≤ Fintype.card V)
    (hheavy : κ * ((Fintype.card V - 1 : ℕ) : ℝ) ≤ ((∑ i, (#(H i) - 1) : ℕ) : ℝ)) :
    ∃ S : Finset V, 2 ≤ #S ∧
      IsWeaklyPartitionConnected (fun i ↦ (H i).subtype (· ∈ S)) κ := by
  set C := (univ : Finset (Finset V)).filter fun S ↦
    2 ≤ #S ∧ κ * ((#S - 1 : ℕ) : ℝ) ≤ ((∑ i, (#(H i ∩ S) - 1) : ℕ) : ℝ) with hC
  have huniv : univ ∈ C := by
    rw [hC, mem_filter]
    refine ⟨mem_univ _, by rwa [card_univ], ?_⟩
    simp only [inter_univ, card_univ]
    exact hheavy
  obtain ⟨S, hS⟩ := C.exists_minimal ⟨univ, huniv⟩
  have hSC := hS.prop
  simp only [hC, mem_filter, mem_univ, true_and] at hSC
  have hcard (i : ι) : #((H i).subtype (· ∈ S)) = #(H i ∩ S) := by
    rw [card_subtype, filter_mem_eq_inter]
  refine ⟨S, hSC.1, isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_⟩
  · simp_rw [hcard, Fintype.card_coe]
    exact hSC.2
  set U' := U.map (Function.Embedding.subtype (· ∈ S))
  have hsub : U' ⊆ S := fun v hv ↦ by
    obtain ⟨u, -, rfl⟩ := mem_map.1 hv
    exact u.2
  have hU'S : U' ⊂ S := by
    obtain ⟨u, -, hu⟩ := (ssubset_iff_of_subset (subset_univ U)).1 hU
    refine (ssubset_iff_of_subset hsub).2 ⟨u, u.2, fun h ↦ hu ?_⟩
    obtain ⟨x, hx, hxu⟩ := mem_map.1 h
    rwa [← Subtype.ext hxu]
  have hcardU : #U' = #U := card_map _
  have hint (i : ι) : #((H i).subtype (· ∈ S) ∩ U) = #(H i ∩ U') := by
    rw [← card_map (Function.Embedding.subtype (· ∈ S)), map_inter, subtype_map,
      filter_mem_eq_inter, inter_assoc, inter_eq_right.2 hsub]
  have hnot : U' ∉ C := fun hC' ↦ hU'S.ne (hS.eq_of_le hC' hU'S.le)
  simp only [hC, mem_filter, mem_univ, true_and, not_and, not_le, hcardU] at hnot
  simp_rw [hint]
  exact (hnot hU2).le
