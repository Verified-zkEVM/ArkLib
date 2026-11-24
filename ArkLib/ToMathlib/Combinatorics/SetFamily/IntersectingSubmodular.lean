/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-!
# Natural-number vectors below an intersecting-submodular set function

Let `V` be a nonempty finite type and `g : Finset V → ℤ` a set function that is submodular on
intersecting pairs, `g (A ∪ B) + g (A ∩ B) ≤ g A + g B` whenever `A ∩ B` is nonempty, and
nonnegative on nonempty sets. If `g univ ≤ ∑ A ∈ P.parts, g A` for every finpartition `P` of
`univ`, then some `δ : V → ℕ` has total `g univ` and satisfies `∑ j ∈ A, δ j ≤ g A` for every
nonempty `A`.

The proof takes a vector `δ` with `∑ j ∈ A, δ j ≤ g A` for every nonempty `A` and of maximal
total. Each `j` then lies in a nonempty set `A` with `∑ i ∈ A, δ i = g A` (a tight set); the union
of two intersecting tight sets is tight; so the relation "lie in a common tight set" is an
equivalence whose classes are tight, and summing over this finpartition gives
`∑ j, δ j ≥ g univ`.

## Main statements

* `Finpartition.exists_forall_mem_parts_of_union`: a covering family of finsets that is closed
  under unions of intersecting pairs contains the parts of some finpartition of `univ`.
* `Finset.exists_nat_sum_eq_and_sum_le_of_intersecting_submodular`: the existence statement above.
-/

@[expose] public section

namespace Finpartition

open Finset

variable {V : Type*}

/-- A predicate on finsets that holds on a set through every point and is closed under unions of
intersecting pairs holds on every part of some finpartition of `univ`. -/
theorem exists_forall_mem_parts_of_union [Fintype V] [DecidableEq V] {p : Finset V → Prop}
    (hunion : ∀ A B : Finset V, (A ∩ B).Nonempty → p A → p B → p (A ∪ B))
    (hcover : ∀ j : V, ∃ A : Finset V, j ∈ A ∧ p A) :
    ∃ P : Finpartition (univ : Finset V), ∀ A ∈ P.parts, p A := by
  classical
  have hmax (j : V) : ∃ M : Finset V, j ∈ M ∧ p M ∧ ∀ A, j ∈ A → p A → A ⊆ M := by
    obtain ⟨M, hM, hMmax⟩ := (univ.filter fun A : Finset V ↦ j ∈ A ∧ p A).exists_max_image card
      (by obtain ⟨A, hA⟩ := hcover j; exact ⟨A, by simpa using hA⟩)
    rw [mem_filter] at hM
    refine ⟨M, hM.2.1, hM.2.2, fun A hjA hA ↦ ?_⟩
    have hU : M = M ∪ A := eq_of_subset_of_card_le subset_union_left <| hMmax _ <| by
      simp [hjA, hunion M A ⟨j, mem_inter.2 ⟨hM.2.1, hjA⟩⟩ hM.2.2 hA]
    exact hU ▸ subset_union_right
  choose M hjM hpM hM using hmax
  let r : Setoid V :=
    { r := fun j k ↦ k ∈ M j
      iseqv := ⟨hjM, fun {j k} h ↦ hM k _ h (hpM j) (hjM j),
        fun {j k _} h1 h2 ↦ hM j _ (hM k _ h1 (hpM j) (hjM j)) (hpM k) h2⟩ }
  refine ⟨ofSetoid r, fun A hA ↦ ?_⟩
  obtain ⟨j, hj⟩ := (ofSetoid r).nonempty_of_mem_parts hA
  have hAM : A = M j := by
    ext k
    rw [← (ofSetoid r).part_eq_of_mem hA hj, mem_part_ofSetoid_iff_rel]
    rfl
  exact hAM ▸ hpM j

end Finpartition

namespace Finset

variable {V : Type*}

/-- If `g` is nonnegative on nonempty sets, some `δ : V → ℕ` with `∑ j ∈ A, δ j ≤ g A` for every
nonempty `A` has maximal total among all such vectors. -/
private theorem exists_forall_sum_le_and_forall_sum_le_sum [Fintype V] {g : Finset V → ℤ}
    (hnonneg : ∀ A : Finset V, A.Nonempty → 0 ≤ g A) :
    ∃ δ : V → ℕ, (∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ g A) ∧
      ∀ δ' : V → ℕ, (∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ' j : ℤ) ≤ g A) →
        ∑ j, δ' j ≤ ∑ j, δ j := by
  classical
  set S := (Fintype.piFinset fun j ↦ range ((g {j}).toNat + 1)).filter
    fun δ : V → ℕ ↦ ∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ g A
  have hS (δ : V → ℕ) (hδ : ∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ g A) : δ ∈ S := by
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j ↦ mem_range.2 ?_, hδ⟩
    have := hδ {j} (singleton_nonempty j)
    rw [sum_singleton] at this
    omega
  obtain ⟨δ, hδS, hmax⟩ := S.exists_max_image (fun δ ↦ ∑ j, δ j)
    ⟨0, hS 0 fun A hA ↦ by simpa using hnonneg A hA⟩
  exact ⟨δ, (mem_filter.1 hδS).2, fun δ' hδ' ↦ hmax δ' (hS δ' hδ')⟩

/-- For a vector `δ` of maximal total with `∑ i ∈ A, δ i ≤ g A` on nonempty sets, every point lies
in a set on which the inequality is an equality. -/
private theorem exists_mem_sum_eq_of_forall_sum_le_sum [Fintype V] {g : Finset V → ℤ}
    {δ : V → ℕ}
    (hδ : ∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ g A)
    (hmax : ∀ δ' : V → ℕ, (∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ' j : ℤ) ≤ g A) →
      ∑ j, δ' j ≤ ∑ j, δ j)
    (j : V) : ∃ A : Finset V, j ∈ A ∧ ∑ i ∈ A, (δ i : ℤ) = g A := by
  classical
  by_contra! h
  have hsum (A : Finset V) :
      ∑ i ∈ A, (δ + Pi.single j 1 : V → ℕ) i = ∑ i ∈ A, δ i + if j ∈ A then 1 else 0 := by
    simp [sum_add_distrib, sum_pi_single']
  have := hmax (δ + Pi.single j 1 : V → ℕ) fun A hA ↦ by
    have h1 := hδ A hA
    rw [← Nat.cast_sum] at h1 ⊢
    rw [hsum]
    split_ifs with hj
    · have h2 := h A hj
      rw [← Nat.cast_sum] at h2
      omega
    · simpa using h1
  rw [hsum univ] at this
  simp at this

/-- If `g` is submodular on intersecting pairs and `∑ i ∈ A, δ i ≤ g A` on nonempty sets, the
union of two intersecting sets on which this is an equality is again such a set. -/
private theorem sum_union_eq_of_sum_eq [DecidableEq V] {g : Finset V → ℤ} {δ : V → ℕ}
    (hsub : ∀ A B : Finset V, (A ∩ B).Nonempty → g (A ∪ B) + g (A ∩ B) ≤ g A + g B)
    (hδ : ∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ g A) {A B : Finset V}
    (hAB : (A ∩ B).Nonempty) (hA : ∑ j ∈ A, (δ j : ℤ) = g A) (hB : ∑ j ∈ B, (δ j : ℤ) = g B) :
    ∑ j ∈ A ∪ B, (δ j : ℤ) = g (A ∪ B) := by
  have h : ∑ j ∈ A ∪ B, (δ j : ℤ) + ∑ j ∈ A ∩ B, (δ j : ℤ) =
      ∑ j ∈ A, (δ j : ℤ) + ∑ j ∈ B, (δ j : ℤ) := sum_union_inter
  linarith [hsub A B hAB, hδ _ hAB, hδ _ (hAB.mono inter_subset_union)]

/-- Let `g : Finset V → ℤ` on a nonempty finite type be submodular on intersecting pairs,
nonnegative on nonempty sets, and satisfy `g univ ≤ ∑ A ∈ P.parts, g A` for every finpartition
`P` of `univ`. Then some `δ : V → ℕ` has `∑ j, δ j = g univ` and `∑ j ∈ A, δ j ≤ g A` for every
nonempty `A`. -/
theorem exists_nat_sum_eq_and_sum_le_of_intersecting_submodular [Fintype V] [DecidableEq V]
    [Nonempty V] {g : Finset V → ℤ}
    (hsub : ∀ A B : Finset V, (A ∩ B).Nonempty → g (A ∪ B) + g (A ∩ B) ≤ g A + g B)
    (hnonneg : ∀ A : Finset V, A.Nonempty → 0 ≤ g A)
    (hpart : ∀ P : Finpartition (univ : Finset V), g univ ≤ ∑ A ∈ P.parts, g A) :
    ∃ δ : V → ℕ, ∑ j, (δ j : ℤ) = g univ ∧
      ∀ A : Finset V, A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ g A := by
  obtain ⟨δ, hδ, hmax⟩ := exists_forall_sum_le_and_forall_sum_le_sum hnonneg
  obtain ⟨P, hP⟩ := Finpartition.exists_forall_mem_parts_of_union
    (p := fun A ↦ ∑ j ∈ A, (δ j : ℤ) = g A)
    (fun _ _ hAB hA hB ↦ sum_union_eq_of_sum_eq hsub hδ hAB hA hB)
    (exists_mem_sum_eq_of_forall_sum_le_sum hδ hmax)
  refine ⟨δ, le_antisymm (hδ univ univ_nonempty) ?_, hδ⟩
  calc g univ ≤ ∑ A ∈ P.parts, g A := hpart P
    _ = ∑ A ∈ P.parts, ∑ j ∈ id A, (δ j : ℤ) := (sum_congr rfl hP).symm
    _ = ∑ j ∈ P.parts.biUnion id, (δ j : ℤ) := (sum_biUnion P.supIndep.pairwiseDisjoint).symm
    _ = ∑ j, (δ j : ℤ) := by rw [P.biUnion_parts]

end Finset
