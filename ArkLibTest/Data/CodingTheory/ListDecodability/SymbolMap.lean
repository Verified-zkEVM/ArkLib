/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
import Mathlib.Data.ZMod.Basic

/-!
# Symbol-map list-size clients

These clients apply the list-size comparison to the inclusion `Bool → ZMod 3`, and show that the
injectivity hypothesis cannot be dropped: the constant map from `Bool` to `Unit` sends the full
code of length one into the full code over `Unit`, yet the first has a list of two codewords at
radius `1` and the second has one codeword in total.
-/

open Code

namespace SymbolMapTest

/-- The inclusion of `Bool` into `ZMod 3` as `0, 1`. -/
def boolToZMod3 : Bool → ZMod 3 := fun b ↦ if b then 1 else 0

theorem boolToZMod3_injective : Function.Injective boolToZMod3 := by
  decide

-- The list sizes of any binary code are bounded by those of its image in `ZMod 3`.
example (C : Set (Fin 4 → Bool)) (δ : ℝ) :
    Lambda C δ ≤ Lambda ((fun c ↦ boolToZMod3 ∘ c) '' C) δ :=
  Lambda_le_of_injective_comp boolToZMod3_injective (fun _ hc ↦ Set.mem_image_of_mem _ hc) δ

-- The pointwise form.
example (C : Set (Fin 4 → Bool)) (f : Fin 4 → Bool) (δ : ℝ) :
    (closeCodewordsRel C f δ).encard ≤
      (closeCodewordsRel ((fun c ↦ boolToZMod3 ∘ c) '' C) (boolToZMod3 ∘ f) δ).encard :=
  encard_closeCodewordsRel_le_of_injective_comp boolToZMod3_injective
    (fun _ hc ↦ Set.mem_image_of_mem _ hc) f δ

-- Injectivity is needed: the full binary code of length one has two codewords within radius `1`
-- of the zero word, while every code over `Unit` has at most one codeword.
example :
    ¬ Lambda (Set.univ : Set (Fin 1 → Bool)) 1 ≤ Lambda (Set.univ : Set (Fin 1 → Unit)) 1 := by
  classical
  intro h
  have hlow : (2 : ℕ∞) ≤ Lambda (Set.univ : Set (Fin 1 → Bool)) 1 := by
    have hlist :
        closeCodewordsRel (Set.univ : Set (Fin 1 → Bool)) (fun _ ↦ false) 1 = Set.univ := by
      ext c
      simp [mem_closeCodewordsRel_iff, relHammingDist_le_one]
    calc (2 : ℕ∞) = (Set.univ : Set (Fin 1 → Bool)).encard := by simp
      _ = _ := by rw [hlist]
      _ ≤ _ := encard_closeCodewordsRel_le_Lambda _ _ _
  have hup : Lambda (Set.univ : Set (Fin 1 → Unit)) 1 ≤ 1 :=
    Lambda_le_iff_forall_encard_le.mpr fun f ↦
      (Set.encard_le_encard (Set.subset_univ _)).trans (by simp)
  exact absurd (hlow.trans (h.trans hup)) (by decide)

end SymbolMapTest
