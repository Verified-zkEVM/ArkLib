/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.InformationTheory.Hamming

/-!
# Hamming distance under coordinate reindexing

`hammingDist_comp` transports the *alphabet* along an injection `α → β`. This file adds the
transport of the *coordinate index*: precomposition with an index equivalence is a Hamming
isometry.

Intended as a candidate for upstreaming to `Mathlib.InformationTheory.Hamming`, next to
`hammingDist_comp`.
-/

@[expose] public section

/-- Reindexing the coordinates by an equivalence preserves Hamming distance. -/
theorem hammingDist_comp_equiv {ι ι' α : Type*} [Fintype ι] [Fintype ι'] [DecidableEq α]
    (e : ι' ≃ ι) (x y : ι → α) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  unfold hammingDist
  apply Finset.card_nbij' (fun i' => e i') (fun i => e.symm i)
  · intro i' hi'; simpa using hi'
  · intro i hi; simpa using hi
  · intro i' hi'; simp
  · intro i hi; simp

/-- Restricting to injectively selected coordinates cannot increase Hamming distance. -/
theorem hammingDist_comp_le_of_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
  classical
  let D := Finset.filter (fun i => x i ≠ y i) Finset.univ
  have hpre : Finset.filter (fun i => x (g i) ≠ y (g i)) Finset.univ =
      D.preimage g hg.injOn := by
    ext i
    simp [D]
  change (Finset.filter (fun i => x (g i) ≠ y (g i)) Finset.univ).card ≤ D.card
  rw [hpre, Finset.card_preimage]
  exact Finset.card_filter_le _ _
