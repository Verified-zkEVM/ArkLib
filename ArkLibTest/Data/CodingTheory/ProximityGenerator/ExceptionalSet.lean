/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet

/-!
# Exceptional-set consumers

An empty exceptional set gives zero error for the full code, including module alphabets and
arbitrary real radii. Taking every seed as exceptional gives the universal probability bound.
-/

open CoreDefinitions LinearCode

example {ι F ℓ S A : Type} [Fintype ι] [Field F] [Fintype ℓ]
    [Nonempty S] [Fintype S] [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (δ : ℝ) :
    mcaError G (⊤ : ModuleCode ι F A) δ = 0 := by
  apply le_antisymm _ bot_le
  have h := mcaError_le_of_exists_exceptional_set_codewords G
    (⊤ : ModuleCode ι F A) δ 0 (fun U => ?_)
  · simpa using h
  · refine ⟨∅, by simp, fun _ _ _ _ _ => ?_⟩
    exact ⟨fun j => ⟨U j, Submodule.mem_top⟩, fun _ _ _ => rfl⟩

example {ι F ℓ S A : Type} [Fintype ι] [Field F] [Fintype ℓ]
    [Nonempty S] [Fintype S] [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ : ℝ) :
    mcaError G MC δ ≤ 1 := by
  classical
  have h := mcaError_le_of_exists_exceptional_set G MC δ (Fintype.card S)
    (fun _ => ⟨Finset.univ, by simp, fun x hx => False.elim (hx (Finset.mem_univ x))⟩)
  simpa [Fintype.card_ne_zero] using h
