/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Alexander Hicks
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finiteness of a set from a uniform bound on its finite subsets

Mathlib has `Set.Infinite.exists_subset_card_eq`, that an infinite set has finite subsets of every
cardinality. This file records the consequence in the direction a counting argument uses it, where
finiteness is the conclusion rather than a hypothesis.
-/

/-- A set whose finite subsets are uniformly bounded is finite.

The bound lives in an arbitrary `FloorSemiring`, so this applies both to a natural bound and to the
real bounds that counting arguments produce. No nonnegativity hypothesis is needed: at a negative
bound the hypothesis at `T = ∅` is already unsatisfiable. -/
theorem Set.finite_of_forall_finset_card_le {α : Type*} {S : Set α} {R : Type*}
    [Semiring R] [LinearOrder R] [FloorSemiring R] {ℓ : R}
    (h : ∀ T : Finset α, (T : Set α) ⊆ S → (T.card : R) ≤ ℓ) : S.Finite := by
  by_contra hinf
  obtain ⟨T, hTS, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊ℓ⌋₊ + 1)
  have hle : ((⌊ℓ⌋₊ + 1 : ℕ) : R) ≤ ℓ := by rw [← hTcard]; exact h T hTS
  have := Nat.le_floor hle
  omega
