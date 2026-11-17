/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exact worst-case probabilities for finite event families

A Boolean event on a nonempty finite challenge space has an exact rational probability.
Taking the largest event count over a finite family computes its worst-case probability
without sampling or deciding arbitrary propositions.
`Probability.maxEventProbability` returns this value in `ℚ≥0`.
`Probability.ofReal_maxEventProbability_eq_iSup` identifies its real embedding with the
`ENNReal` supremum of counting probabilities.

The definitions require executable finite enumerations and a Boolean event.
The exhaustive search can be expensive even when evaluating one event is efficient.
-/

@[expose] public section

open Finset

namespace Probability

variable {W S : Type*} [Fintype W] [Fintype S]

/-- The largest number of challenges satisfying an event in a finite family. -/
def maxEventCount (bad : W → S → Bool) : ℕ :=
  (Finset.univ : Finset W).sup fun w ↦ #{c : S | bad w c = true}

/-- The exact worst-case event probability, computed as a nonnegative rational.

The value is zero for an empty family or challenge space. -/
def maxEventProbability (bad : W → S → Bool) : ℚ≥0 :=
  (maxEventCount bad : ℚ≥0) / (Fintype.card S : ℚ≥0)

/-- Every member of the family has at most the maximum event count. -/
theorem eventCount_le_maxEventCount (bad : W → S → Bool) (w : W) :
    #{c : S | bad w c = true} ≤ maxEventCount bad := by
  unfold maxEventCount
  exact Finset.le_sup (f := fun w : W ↦ #{c : S | bad w c = true}) (Finset.mem_univ w)

/-- The maximum event count is bounded by the size of the challenge space. -/
theorem maxEventCount_le_card (bad : W → S → Bool) :
    maxEventCount bad ≤ Fintype.card S := by
  apply Finset.sup_le
  intro w _
  exact Finset.card_filter_le _ _

/-- The maximum event probability is at most one, including empty finite spaces. -/
theorem maxEventProbability_le_one (bad : W → S → Bool) : maxEventProbability bad ≤ 1 := by
  unfold maxEventProbability
  apply div_le_one_of_le₀
  · exact Nat.cast_le.mpr (maxEventCount_le_card bad)
  · positivity

/-- The computed rational probability embeds as the supremum of uniform counting probabilities. -/
theorem ofReal_maxEventProbability_eq_iSup (bad : W → S → Bool) :
    ENNReal.ofReal (maxEventProbability bad : ℝ) =
      ⨆ w : W, ENNReal.ofReal
        ((#{c : S | bad w c = true} : ℝ) / Fintype.card S) := by
  cases isEmpty_or_nonempty W with
  | inl h =>
    let : IsEmpty W := h
    simp [maxEventProbability, maxEventCount]
  | inr h =>
    let : Nonempty W := h
    simp only [maxEventProbability, NNRat.cast_div, NNRat.cast_natCast]
    apply le_antisymm
    · obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun w : W ↦ #{c : S | bad w c = true})
      unfold maxEventCount
      rw [hw]
      exact le_iSup (fun w : W ↦ ENNReal.ofReal
        ((#{c : S | bad w c = true} : ℝ) / Fintype.card S)) w
    · refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (eventCount_le_maxEventCount bad w))
        (Nat.cast_nonneg _)

end Probability
