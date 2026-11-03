/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for line-decoding MCA bounds -/

namespace LineDecodingTest

open CodingTheory

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def u₀ : Fin 2 → ZMod 2 := ![0, 1]

private def u₁ : Fin 2 → ZMod 2 := ![1, 1]

private def c₀ : Fin 2 → ZMod 2 := 0

private def c₁ : Fin 2 → ZMod 2 := 0

private def G (γ : ZMod 2) : Finset (Fin 2) := if γ = 0 then {0} else {1}

/-- The hypotheses of `card_le_floor_add_one_of_pencil_mismatch` hold over `ZMod 2` with two
coordinates, `e = 1` and both challenges. -/
example :
    (∀ γ ∈ (Finset.univ : Finset (ZMod 2)), Fintype.card (Fin 2) - 1 ≤ (G γ).card) ∧
    (∀ γ ∈ (Finset.univ : Finset (ZMod 2)), ∀ i ∈ G γ,
      u₀ i + γ • u₁ i = c₀ i + γ • c₁ i) ∧
    (∀ γ ∈ (Finset.univ : Finset (ZMod 2)), ∃ i ∈ G γ, u₀ i ≠ c₀ i ∨ u₁ i ≠ c₁ i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- On that instance the bound `|E| ≤ e + 1` is an equality: the count is sharp. -/
example : (Finset.univ : Finset (ZMod 2)).card = 1 + 1 := by
  decide

/-- The bound applied to the instance. -/
example : (Finset.univ : Finset (ZMod 2)).card ≤ 1 + 1 :=
  card_le_floor_add_one_of_pencil_mismatch Finset.univ u₀ u₁ c₀ c₁ 1 G
    (by decide) (by decide) (by decide)

end LineDecodingTest
