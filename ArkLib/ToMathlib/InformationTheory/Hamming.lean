/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.InformationTheory.Hamming

/-!
# Hamming distance under coordinate reindexing

`hammingDist_comp` transports the *alphabet* along an injection `α → β`. This file adds the
transport of the *coordinate index*: precomposition with an index equivalence is a Hamming
isometry.

Intended as a candidate for upstreaming to `Mathlib.InformationTheory.Hamming`, next to
`hammingDist_comp`.
-/

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
