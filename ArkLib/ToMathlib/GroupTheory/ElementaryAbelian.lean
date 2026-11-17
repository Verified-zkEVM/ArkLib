/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Coordinates for finite abelian groups of exponent two

A finite abelian group in which `x + x = 0` is a vector space over `ZMod 2`.
Its cardinality determines a decomposition into two blocks of binary coordinates.

## Main statements

* `AddCommGroup.nonempty_addEquiv_zmod_two_prod`: coordinates with prescribed block sizes.
-/

@[expose] public section

namespace AddCommGroup

/-- A finite group with `x + x = 0` and `2 ^ (v + w)` elements is `(ZMod 2) ^ v × (ZMod 2) ^ w`. -/
theorem nonempty_addEquiv_zmod_two_prod {G : Type*} [AddCommGroup G] [Finite G]
    (h2 : ∀ x : G, x + x = 0) {v w : ℕ} (hG : Nat.card G = 2 ^ (v + w)) :
    Nonempty (G ≃+ (Fin v → ZMod 2) × (Fin w → ZMod 2)) := by
  let : Module (ZMod 2) G :=
    AddCommGroup.zmodModule (n := 2) (fun x ↦ by rw [two_nsmul]; exact h2 x)
  have : Fintype G := Fintype.ofFinite G
  have h1 : Fintype.card G = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) G :=
    Module.card_eq_pow_finrank
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hG] at h1
  have h3 : Module.finrank (ZMod 2) G =
      Module.finrank (ZMod 2) ((Fin v → ZMod 2) × (Fin w → ZMod 2)) := by
    rw [← Nat.pow_right_injective (le_refl 2) h1, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun]
  exact ⟨(LinearEquiv.ofFinrankEq _ _ h3).toAddEquiv⟩

end AddCommGroup
