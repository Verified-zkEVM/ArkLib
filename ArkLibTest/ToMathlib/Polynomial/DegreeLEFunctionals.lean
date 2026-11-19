/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.Polynomial.DegreeLEFunctionals
import Mathlib.Data.Rat.Init

/-! # Acceptance cases for functionals cutting out bounded-degree polynomials -/

open Polynomial

-- The line spanned by `X` inside polynomials of degree at most `1` over `ℚ`.
-- Every list given by the statement kills `X`, and a polynomial of degree at most one that it
-- kills is a multiple of `X`.
example : ∃ l : List (ℚ[X] →ₗ[ℚ] ℚ), (∀ Λ ∈ l, Λ X = 0) ∧
    ∀ H : ℚ[X], H.degree ≤ 1 → (∀ Λ ∈ l, Λ H = 0) → H ∈ Submodule.span ℚ {X} := by
  obtain ⟨l, h₁, h₂⟩ := exists_list_linearMap_of_le_degreeLE (E := ℚ) (N := 1)
    (V := Submodule.span ℚ {X}) (by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_degreeLE]
      exact degree_X_le)
  exact ⟨l, fun Λ hΛ ↦ h₁ Λ hΛ X (Submodule.subset_span rfl), h₂⟩

-- The zero space is cut out: a polynomial of degree at most `2` killed by the list is `0`.
example : ∃ l : List (ℚ[X] →ₗ[ℚ] ℚ),
    ∀ H : ℚ[X], H.degree ≤ 2 → (∀ Λ ∈ l, Λ H = 0) → H = 0 := by
  obtain ⟨l, -, h₂⟩ := exists_list_linearMap_of_le_degreeLE (E := ℚ) (N := 2)
    (V := ⊥) bot_le
  exact ⟨l, fun H hH hl ↦ (Submodule.mem_bot ℚ).mp (h₂ H hH hl)⟩

/-- info: 'Polynomial.exists_list_linearMap_of_le_degreeLE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.exists_list_linearMap_of_le_degreeLE
