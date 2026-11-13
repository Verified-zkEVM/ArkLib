/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.Defs

/-!
# Row orbits and large lists

A code containing the columns of a matrix in one Hamming ball has a large list, and both properties
of the columns used for this are invariant under permuting the rows.

## Main statements

* `CodingTheory.RandomLinearInternal.lambda_ge_of_contains`: a code that contains `L` independent
  words in one Hamming ball of radius `⌊δ n⌋` has `Λ ≥ L`.
* `CodingTheory.RandomLinearInternal.exists_center_of_mem_rowOrbit`,
  `CodingTheory.RandomLinearInternal.linearIndependent_cols_of_mem_rowOrbit`: closeness to a common
  centre and column independence are invariant under row permutation.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

open Code

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [Fintype F] in
/-- A code containing `L` independent words in one ball of radius `⌊δ n⌋` has `Λ ≥ L`. -/
theorem lambda_ge_of_contains (δ : ℝ) (hδ : 0 ≤ δ) {L : ℕ} (C : Submodule F (ι → F))
    (M : ι → Fin L → F) (hM : LinearIndependent F (Function.swap M))
    (hC : ∀ i, Function.swap M i ∈ C)
    (z : ι → F) (hz : ∀ i, hammingDist (Function.swap M i) z ≤ ⌊δ * Fintype.card ι⌋₊) :
    ((L : ℕ) : ℕ∞) ≤ Code.Lambda (C : Set (ι → F)) δ := by
  have hsub : Set.range (Function.swap M) ⊆ closeCodewordsRel (C : Set (ι → F)) z δ := by
    rintro _ ⟨i, rfl⟩
    rw [closeCodewordsRel_eq_setOf _ δ hδ]
    exact ⟨hC i, hz i⟩
  have h := encard_le_Lambda_of_subset_closeCodewordsRel hsub
  rwa [hM.injective.encard_range, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin] at h

omit [Field F] [DecidableEq ι] [Fintype F] in
/-- Closeness of the columns to a common centre is invariant under row permutation. -/
theorem exists_center_of_mem_rowOrbit {L : ℕ} {M₀ M : ι → Fin L → F} (hM : M ∈ rowOrbit M₀)
    (r : ℕ) (z : ι → F) (hz : ∀ i, hammingDist (Function.swap M₀ i) z ≤ r) :
    ∃ z' : ι → F, ∀ i, hammingDist (Function.swap M i) z' ≤ r := by
  obtain ⟨σ, rfl⟩ := mem_rowOrbit.1 hM
  refine ⟨z ∘ σ, fun i => ?_⟩
  have : Function.swap (M₀ ∘ σ) i = Function.swap M₀ i ∘ σ := rfl
  rw [this]
  refine le_trans (le_of_eq ?_) (hz i)
  exact Finset.card_equiv σ (by simp)

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Column independence is invariant under row permutation. -/
theorem linearIndependent_cols_of_mem_rowOrbit {L : ℕ} {M₀ M : ι → Fin L → F}
    (hM : M ∈ rowOrbit M₀) (h : LinearIndependent F (Function.swap M₀)) :
    LinearIndependent F (Function.swap M) := by
  obtain ⟨σ, rfl⟩ := mem_rowOrbit.1 hM
  exact h.map' _
    (LinearMap.ker_eq_bot.2 (LinearMap.funLeft_injective_of_surjective F F σ σ.surjective))

end CodingTheory.RandomLinearInternal
