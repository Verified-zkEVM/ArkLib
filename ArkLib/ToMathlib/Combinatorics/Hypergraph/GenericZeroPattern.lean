/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.ToMathlib.Combinatorics.Hypergraph.PartitionConnected
public import ArkLib.ToMathlib.Combinatorics.SetFamily.GenericZeroPattern
public import ArkLib.ToMathlib.Combinatorics.SetFamily.IntersectingSubmodular

/-!
# Generic zero patterns from weakly partition-connected hypergraphs

Let `H : ι → Finset V` be a `k`-weakly partition-connected hypergraph with `N = card ι` nonempty
edges. Then the vertices can be listed, with repetitions, as `f : Fin (N - k) → V` so that the
sets of edges avoiding them, `ℓ ↦ {i | f ℓ ∉ H i}`, form a generic zero pattern: for every
nonempty `I`, at most `N - k - #I` edges avoid all of `I.image f`.

The multiplicities come from `Finset.exists_nat_sum_eq_and_sum_le_of_intersecting_submodular`
applied to `A ↦ #{i | (H i ∩ A).Nonempty} - k` (in `ℤ`): this set function is submodular on
intersecting pairs, nonnegative on nonempty sets, and its partition condition is weak
partition-connectivity.
This replaces the hypergraph orientation theorem used in [AGL24]; no orientations appear.

## Main statements

* `IsWeaklyPartitionConnected.exists_sum_add_eq_card`: multiplicities `δ : V → ℕ` with
  `∑ j, δ j + k = N` and `∑ j ∈ A, δ j + k ≤ #{i | (H i ∩ A).Nonempty}` for every nonempty `A`.
* `IsWeaklyPartitionConnected.exists_isGenericZeroPattern`: the generic zero pattern above.

`exists_isGenericZeroPattern` is the corollary of [AGL24] that a `k`-weakly partition-connected
hypergraph gives a generic zero pattern, which [AGL24] says essentially captures the hard direction
of [BGM23, Lemma 2.8]. Nonempty edges are needed: an empty edge lies in every set
`{i | f ℓ ∉ H i}`, so the condition fails for `I = univ` unless `card ι ≤ k`.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
* [Brakensiek, J., Gopi, S., and Makam, V., *Generic Reed-Solomon codes achieve list-decoding
    capacity*][BGM23]
-/

@[expose] public section

open Finset

/-- A vector `δ : V → ℕ` of total `m` counts the fibers of some map `Fin m → V`. -/
private theorem exists_card_filter_mem_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (δ : V → ℕ) {m : ℕ} (hm : ∑ j, δ j = m) :
    ∃ f : Fin m → V, ∀ A : Finset V, #{ℓ | f ℓ ∈ A} = ∑ j ∈ A, δ j := by
  subst hm
  let e : (Σ j : V, Fin (δ j)) ≃ Fin (∑ j, δ j) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp)
  refine ⟨fun ℓ ↦ (e.symm ℓ).1, fun A ↦ ?_⟩
  calc #{ℓ | (e.symm ℓ).1 ∈ A} = #(A.sigma fun j ↦ (univ : Finset (Fin (δ j)))) :=
        card_equiv e.symm (by simp)
    _ = ∑ j ∈ A, δ j := by simp [card_sigma]

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V] {H : ι → Finset V} {k : ℕ}

/-- If a `k`-weakly partition-connected hypergraph has nonempty edges and at least `k` of them,
there are multiplicities `δ : V → ℕ` with `∑ j, δ j + k = card ι` such that every nonempty vertex
set `A` meets at least `∑ j ∈ A, δ j + k` edges. -/
theorem IsWeaklyPartitionConnected.exists_sum_add_eq_card (h : IsWeaklyPartitionConnected H k)
    (hH : ∀ i, (H i).Nonempty) (hk : k ≤ Fintype.card ι) :
    ∃ δ : V → ℕ, ∑ j, δ j + k = Fintype.card ι ∧
      ∀ A : Finset V, A.Nonempty → ∑ j ∈ A, δ j + k ≤ #{i | (H i ∩ A).Nonempty} := by
  have huniv : #{i | (H i ∩ univ).Nonempty} = Fintype.card ι := by
    simp only [inter_univ, filter_true_of_mem fun i _ ↦ hH i, card_univ]
  rcases isEmpty_or_nonempty V with hV | hV
  · have : IsEmpty ι := ⟨fun i ↦ (hH i).elim fun v _ ↦ hV.false v⟩
    refine ⟨fun _ ↦ 0, ?_, fun A hA ↦ absurd hA (by simp [eq_empty_of_isEmpty A])⟩
    rw [Fintype.card_eq_zero] at hk ⊢
    simp only [univ_eq_empty, sum_empty]
    omega
  have hsub : ∀ A B : Finset V, (A ∩ B).Nonempty →
      ((#{i | (H i ∩ (A ∪ B)).Nonempty} : ℤ) - k) + ((#{i | (H i ∩ (A ∩ B)).Nonempty} : ℤ) - k) ≤
        ((#{i | (H i ∩ A).Nonempty} : ℤ) - k) + ((#{i | (H i ∩ B).Nonempty} : ℤ) - k) := by
    classical
    intro A B _
    have hunion : univ.filter (fun i ↦ (H i ∩ (A ∪ B)).Nonempty) =
        univ.filter (fun i ↦ (H i ∩ A).Nonempty) ∪ univ.filter fun i ↦ (H i ∩ B).Nonempty := by
      ext i
      simp [inter_union_distrib_left, union_nonempty]
    have hinter : univ.filter (fun i ↦ (H i ∩ (A ∩ B)).Nonempty) ⊆
        univ.filter (fun i ↦ (H i ∩ A).Nonempty) ∩ univ.filter fun i ↦ (H i ∩ B).Nonempty :=
      fun i hi ↦ by
        simp only [mem_filter, mem_univ, true_and, mem_inter] at hi ⊢
        exact ⟨hi.mono (inter_subset_inter_left inter_subset_left),
          hi.mono (inter_subset_inter_left inter_subset_right)⟩
    have h1 := card_union_add_card_inter (univ.filter fun i ↦ (H i ∩ A).Nonempty)
      (univ.filter fun i ↦ (H i ∩ B).Nonempty)
    have h2 := card_le_card hinter
    rw [← hunion] at h1
    omega
  have hnonneg : ∀ A : Finset V, A.Nonempty → 0 ≤ (#{i | (H i ∩ A).Nonempty} : ℤ) - k := by
    intro A hA
    rw [sub_nonneg]
    by_cases hAu : A = univ
    · rw [hAu, huniv]
      exact_mod_cast hk
    obtain ⟨v, hv⟩ := hA
    obtain ⟨w, hw⟩ : ∃ w, w ∉ A := not_forall.1 fun h' ↦ hAu (eq_univ_of_forall h')
    have : Nontrivial V := ⟨⟨v, w, fun hvw ↦ hw (hvw ▸ hv)⟩⟩
    exact_mod_cast h.le_card_filter_inter_nonempty ⟨v, hv⟩
  have hpart : ∀ P : Finpartition (univ : Finset V),
      (#{i | (H i ∩ univ).Nonempty} : ℤ) - k ≤
        ∑ A ∈ P.parts, ((#{i | (H i ∩ A).Nonempty} : ℤ) - k) := by
    simpa only [inter_univ] using (isWeaklyPartitionConnected_natCast_iff H k).1 h
  obtain ⟨δ, hsum, hle⟩ :=
    exists_nat_sum_eq_and_sum_le_of_intersecting_submodular hsub hnonneg hpart
  refine ⟨δ, ?_, fun A hA ↦ ?_⟩
  · rw [huniv, ← Nat.cast_sum] at hsum
    omega
  · have := hle A hA
    rw [← Nat.cast_sum] at this
    omega

/-- **Generic zero patterns from weakly partition-connected hypergraphs.** If `H : ι → Finset V`
is `k`-weakly partition-connected and all edges are nonempty, then there is a list of vertices
`f : Fin (card ι - k) → V` such that the sets `{i | f ℓ ∉ H i}` of edges avoiding them form a
generic zero pattern.

The edges must be nonempty, but an agreement hypergraph can have empty edges: no word agrees with
the received word at that coordinate. To apply this theorem, first drop the empty edges with
`isWeaklyPartitionConnected_restrict_edges_iff`, which keeps weak partition-connectivity because an
edge with at most one vertex does not count. -/
theorem IsWeaklyPartitionConnected.exists_isGenericZeroPattern [DecidableEq ι]
    (h : IsWeaklyPartitionConnected H k) (hH : ∀ i, (H i).Nonempty) :
    ∃ f : Fin (Fintype.card ι - k) → V,
      IsGenericZeroPattern (Fintype.card ι - k) fun ℓ ↦ {i | f ℓ ∉ H i} := by
  by_cases hk : k ≤ Fintype.card ι
  swap
  · exact ⟨fun ℓ ↦ absurd ℓ.2 (by omega), fun I hI ↦ absurd hI.choose.2 (by omega)⟩
  obtain ⟨δ, hsum, hδ⟩ := h.exists_sum_add_eq_card hH hk
  obtain ⟨f, hf⟩ := exists_card_filter_mem_eq_sum δ (m := Fintype.card ι - k) (by omega)
  refine ⟨f, fun I hI ↦ ?_⟩
  have hinf : I.inf' hI (fun ℓ ↦ univ.filter fun i ↦ f ℓ ∉ H i) =
      univ.filter fun i ↦ ¬(H i ∩ I.image f).Nonempty := by
    ext i
    rw [mem_inf']
    simp only [mem_filter, mem_univ, true_and, not_nonempty_iff_eq_empty,
      eq_empty_iff_forall_notMem, mem_inter, mem_image, not_and]
    exact ⟨fun h' v hv ⟨ℓ, hℓ, hfv⟩ ↦ h' ℓ hℓ (hfv ▸ hv),
      fun h' ℓ hℓ hv ↦ h' (f ℓ) hv ⟨ℓ, hℓ, rfl⟩⟩
  have hcompl := card_filter_add_card_filter_not (s := univ) fun i ↦ (H i ∩ I.image f).Nonempty
  rw [card_univ] at hcompl
  have hI' : #I ≤ ∑ j ∈ I.image f, δ j := by
    rw [← hf]
    exact card_le_card fun ℓ hℓ ↦ by simpa using ⟨ℓ, hℓ, rfl⟩
  have := hδ (I.image f) (hI.image f)
  rw [hinf]
  omega
