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

private def u₀ : Fin 2 → ZMod 2 := ![0, 1]

private def u₁ : Fin 2 → ZMod 2 := ![1, 1]

private def c₀ : Fin 2 → ZMod 2 := 0

private def c₁ : Fin 2 → ZMod 2 := 0

private def G (γ : ZMod 2) : Finset (Fin 2) := if γ = 0 then {0} else {1}

/-- The root-set count `card_le_add_one_of_pencil_mismatch` is sharp: over `ZMod 2` with two
coordinates and `e = 1`, both challenges satisfy its hypotheses, so `|E| = e + 1`. -/
example : (Finset.univ : Finset (ZMod 2)).card = 1 + 1 ∧
    (Finset.univ : Finset (ZMod 2)).card ≤ 1 + 1 :=
  ⟨by decide, card_le_add_one_of_pencil_mismatch Finset.univ u₀ u₁ c₀ c₁ 1 G
    (by decide) (by decide) (by decide)⟩

end LineDecodingTest
