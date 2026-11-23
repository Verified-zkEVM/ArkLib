/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exact worst-case probabilities for finite event families

Consider a finite family of Boolean events on a finite challenge space.
`Probability.maxEventProbability` divides the largest event count in the family by the size of
the challenge space. It returns this exact worst-case probability in `ℚ≥0` by exhaustive
counting.
`Probability.ofReal_maxEventProbability_eq_iSup` proves that `ENNReal.ofReal` of its real cast is
the `ENNReal` supremum of the counting probabilities.
`Probability.ofReal_maxEventProbability_eq_iSup_of_iff` gives the same supremum for a
propositional event that the Boolean event decides.

The definitions use no classical decision procedure and no sampler. Execution requires executable
`Fintype` enumerations and an executable Boolean event. The count evaluates the event once for each
pair of a family member and a challenge.
-/

@[expose] public section

open Finset

namespace Probability

variable {W S : Type*} [Fintype W] [Fintype S]

/-- The largest number of challenges `c` that satisfy `bad w c`, over the members `w` of a
finite family. -/
def maxEventCount (bad : W → S → Bool) : ℕ :=
  (Finset.univ : Finset W).sup fun w ↦ #{c : S | bad w c = true}

/-- The exact worst-case probability of the events `bad w`, as a nonnegative rational: the
largest event count divided by the size of the challenge space.

The value is zero for an empty family or an empty challenge space. -/
def maxEventProbability (bad : W → S → Bool) : ℚ≥0 :=
  (maxEventCount bad : ℚ≥0) / (Fintype.card S : ℚ≥0)

/-- The event count of every member of the family is at most `maxEventCount bad`. -/
theorem card_filter_le_maxEventCount (bad : W → S → Bool) (w : W) :
    #{c : S | bad w c = true} ≤ maxEventCount bad :=
  Finset.le_sup (f := fun w : W ↦ #{c : S | bad w c = true}) (Finset.mem_univ w)

/-- `ENNReal.ofReal` of the real cast of the exact worst-case probability is the supremum, over the
family, of the uniform counting probabilities. -/
theorem ofReal_maxEventProbability_eq_iSup (bad : W → S → Bool) :
    ENNReal.ofReal (maxEventProbability bad : ℝ) =
      ⨆ w : W, ENNReal.ofReal ((#{c : S | bad w c = true} : ℝ) / Fintype.card S) := by
  rcases isEmpty_or_nonempty W with hW | hW
  · simp [maxEventProbability, maxEventCount]
  · simp only [maxEventProbability, NNRat.cast_div, NNRat.cast_natCast]
    apply le_antisymm
    · obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun w : W ↦ #{c : S | bad w c = true})
      unfold maxEventCount
      rw [hw]
      exact le_iSup (fun w : W ↦ ENNReal.ofReal
        ((#{c : S | bad w c = true} : ℝ) / Fintype.card S)) w
    · refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_filter_le_maxEventCount bad w))
        (Nat.cast_nonneg _)

/-- Suppose that `bad w c = true` holds exactly when `p w c` holds. Then `ENNReal.ofReal` of the
real cast of `maxEventProbability bad` is the supremum, over the family, of the uniform counting
probabilities of `p`. -/
theorem ofReal_maxEventProbability_eq_iSup_of_iff (bad : W → S → Bool) (p : W → S → Prop)
    [∀ w, DecidablePred (p w)] (h : ∀ w c, bad w c = true ↔ p w c) :
    ENNReal.ofReal (maxEventProbability bad : ℝ) =
      ⨆ w : W, ENNReal.ofReal ((#{c : S | p w c} : ℝ) / Fintype.card S) := by
  rw [ofReal_maxEventProbability_eq_iSup]
  simp only [h]

end Probability
