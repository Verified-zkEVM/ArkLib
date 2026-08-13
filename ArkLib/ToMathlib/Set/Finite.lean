/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Alexander Hicks
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Finiteness of a set from a uniform bound on its finite subsets

A set whose finite subsets all have cardinality at most `ℓ` is itself finite. Mathlib has the
contrapositive ingredient — `Set.Infinite.exists_subset_card_eq`, an infinite set has finite
subsets of *every* cardinality — but not this consequence, which is the form actually used when a
counting argument delivers a bound on finite families and finiteness is wanted as a conclusion
rather than assumed as a hypothesis.

The bound is real-valued rather than natural because that is the form counting arguments arrive at
(Johnson-type bounds are real), and because it subsumes the natural-number case by a cast. No
sign hypothesis is needed: at `ℓ < 0` the hypothesis is already unsatisfiable, `T = ∅` giving
`0 ≤ ℓ`.
-/

/-- **A set all of whose finite subsets are uniformly bounded is finite.**

Mathlib provides `Set.Infinite.exists_subset_card_eq` but not this consequence of it. Stated with a
real bound, which is what a counting argument produces and which covers a natural bound by a cast.

Note this is *not* vacuous for negative `ℓ`: the hypothesis instantiated at `T = ∅` gives
`0 ≤ ℓ`, so a negative bound makes the hypothesis unsatisfiable rather than the conclusion free. -/
theorem Set.Finite.of_forall_finset_card_le {α : Type*} {S : Set α} {ℓ : ℝ}
    (h : ∀ T : Finset α, (T : Set α) ⊆ S → (T.card : ℝ) ≤ ℓ) : S.Finite := by
  by_contra hinf
  obtain ⟨T, hTS, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊ℓ⌋₊ + 1)
  have hle := h T hTS
  rw [hTcard] at hle
  have := Nat.lt_floor_add_one ℓ
  push_cast at hle
  linarith
