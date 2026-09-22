/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Staircase counts

The staircase of slope `D` and length `L` is the set of pairs `(x, b)` of natural numbers with
`x + D * b < L`. For each `b < L` it contains the `L - D * b` values `x < L - D * b`, so it has
`staircaseCount D L = ∑_{b < L} (L - D * b)` elements. The terms with `D * b ≥ L` vanish in
truncated subtraction.

`Finset.staircase D L` cuts the pairs to `x, b < L`. For `D > 0` the cut removes nothing, since
`b ≤ D * b < L`. For `D = 0` the condition `x < L` does not bound `b`, and the cut keeps the set
finite: `Finset.staircase 0 L` has `L * L` elements, while the set of all pairs is infinite once
`L > 0`.

## Main statements

* `Finset.mem_staircase_of_pos`: for `D > 0`, membership is the inequality `x + D * b < L`.
* `Finset.card_staircase`: `#(staircase D L) = staircaseCount D L` for every `D`.
* `Nat.card_staircasePairs`: for `D > 0` the type of all natural pairs with `x + D * b < L` has
  `staircaseCount D L` elements.

## References

Generalizes `staircaseCount`, `StaircaseIndex`, `card_staircaseIndex`, `staircaseIndexEquiv`, and
`card_staircasePairs` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Counting.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source counted a dependent index type
`Σ b : Fin L, Fin (L - D * b)` and transported it by an explicit equivalence; here the pairs form
a filtered product `Finset`, its cardinality needs no hypothesis on `D`, and only the comparison
with the unbounded subtype assumes `D > 0`.
-/

@[expose] public section

open Finset

namespace Nat

/-- The staircase count `∑_{b < L} (L - D * b)`, the number of natural pairs `(x, b)` with
`x + D * b < L` when `D > 0`. At `D = 0` it is `L * L`. -/
def staircaseCount (D L : ℕ) : ℕ :=
  ∑ b ∈ range L, (L - D * b)

/-- A staircase of length zero is empty. -/
@[simp]
theorem staircaseCount_zero_right (D : ℕ) : staircaseCount D 0 = 0 := by
  simp [staircaseCount]

end Nat

namespace Finset

/-- The pairs `(x, b)` with `x + D * b < L`, cut to `x < L` and `b < L`. The cut on `b` matters
only when `D = 0`. -/
def staircase (D L : ℕ) : Finset (ℕ × ℕ) :=
  (range L ×ˢ range L).filter fun p => p.1 + D * p.2 < L

/-- Membership in the staircase for any `D`: the inequality together with the cut `b < L`. -/
theorem mem_staircase {D L : ℕ} {p : ℕ × ℕ} :
    p ∈ staircase D L ↔ p.1 + D * p.2 < L ∧ p.2 < L := by
  simp only [staircase, mem_filter, mem_product, mem_range]
  omega

/-- For `D > 0` membership in the staircase is the inequality `x + D * b < L` alone. At `D = 0`
the pair `(0, L)` satisfies `0 + 0 * L < L` for `L > 0` but is not in the staircase. -/
theorem mem_staircase_of_pos {D L : ℕ} (hD : 0 < D) {p : ℕ × ℕ} :
    p ∈ staircase D L ↔ p.1 + D * p.2 < L := by
  rw [mem_staircase]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  have : p.2 ≤ D * p.2 := Nat.le_mul_of_pos_left _ hD
  omega

/-- The staircase has `∑_{b < L} (L - D * b)` elements: the fiber over `b` is
`{x | x < L - D * b}`. This holds for every `D`. -/
theorem card_staircase (D L : ℕ) : #(staircase D L) = Nat.staircaseCount D L := by
  rw [staircase, card_filter, sum_product_right, Nat.staircaseCount]
  refine sum_congr rfl fun b _ => ?_
  rw [← card_filter]
  have : (range L).filter (fun x => x + D * b < L) = range (L - D * b) := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]

end Finset

namespace Nat

/-- For `D > 0` there are exactly `staircaseCount D L` natural pairs `(x, b)` with
`x + D * b < L`. The hypothesis is needed: at `D = 0` and `L > 0` every pair `(0, b)` qualifies,
the type is infinite, and its `Nat.card` is `0`. -/
theorem card_staircasePairs {D : ℕ} (hD : 0 < D) (L : ℕ) :
    Nat.card {p : ℕ × ℕ // p.1 + D * p.2 < L} = staircaseCount D L := by
  rw [← card_staircase, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_staircase_of_pos hD).symm)

end Nat
