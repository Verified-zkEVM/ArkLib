/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.Combinatorics.SetFamily.GenericZeroPattern
import ArkLib.ToMathlib.Combinatorics.SetFamily.IntersectingSubmodular
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for set families

Vectors below an intersecting-submodular set function, and generic zero patterns, which `decide`
checks without the polynomial development.
-/

open Finset

/-- The cardinality function on `Fin 3` satisfies the hypotheses, so some vector of total `3` lies
below it. -/
example : ∃ δ : Fin 3 → ℕ, ∑ j, (δ j : ℤ) = 3 ∧
    ∀ A : Finset (Fin 3), A.Nonempty → ∑ j ∈ A, (δ j : ℤ) ≤ #A := by
  obtain ⟨δ, hsum, hle⟩ :=
    exists_nat_sum_eq_and_sum_le_of_intersecting_submodular (g := fun A : Finset (Fin 3) ↦ (#A : ℤ))
      (fun A B _ ↦ by exact_mod_cast (card_union_add_card_inter A B).le)
      (fun A _ ↦ Int.natCast_nonneg _)
      (fun P ↦ by exact_mod_cast P.sum_card_parts.ge)
  exact ⟨δ, by simpa using hsum, hle⟩

/-- A generic zero pattern whose first set has fewer than `3 - 1` elements. -/
example : IsGenericZeroPattern 3 (![{0}, {1, 2}, {2, 3}] : Fin 3 → Finset (Fin 4)) := by
  decide

/-- Two equal sets of size `2` violate the condition: `#({0, 1} ∩ {0, 1}) + 2 = 4 > 3`. -/
example : ¬ IsGenericZeroPattern 3 (![{0, 1}, {0, 1}, {2, 3}] : Fin 3 → Finset (Fin 4)) := by
  decide
