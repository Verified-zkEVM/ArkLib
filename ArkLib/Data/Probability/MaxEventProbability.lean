/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi

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

`Probability.maxEventCountWithReply` counts events when a reply can depend on a first challenge.
It evaluates the event once per context, first challenge, reply, and second challenge.
`Probability.maxEventCount_eq_maxEventCountWithReply` proves that this count agrees with the
maximum over message functions.
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

section Reply

variable {T Reply : Type*} [Fintype T] [Fintype Reply]

/-- The maximum event count over contexts when a reply observes the first challenge.

For each context and first challenge `t : T`, the count maximizes over replies, scoring each
reply over all second challenges `s : S`. It sums these maxima over `t` and takes the maximum
over contexts. For nonempty challenge spaces, division by `card T * card S` gives the largest
event probability over contexts and reply functions under independent uniform challenges. -/
def maxEventCountWithReply (bad : W → T → Reply → S → Bool) : ℕ :=
  (univ : Finset W).sup fun w ↦ ∑ t : T, maxEventCount (bad w t)

private theorem sup_pi_sum_eq_sum_sup [DecidableEq T] (score : T → Reply → ℕ) :
    (univ : Finset (T → Reply)).sup (fun reply ↦ ∑ t, score t (reply t)) =
      ∑ t, (univ : Finset Reply).sup (score t) := by
  apply le_antisymm
  · exact Finset.sup_le_iff.mpr fun reply _ ↦ sum_le_sum fun t _ ↦
      le_sup (f := score t) (mem_univ (reply t))
  · rcases isEmpty_or_nonempty Reply with hReply | hReply
    · simp
    have hmax (t : T) : ∃ r : Reply, univ.sup (score t) = score t r := by
      obtain ⟨r, _, hr⟩ := exists_mem_eq_sup univ univ_nonempty (score t)
      exact ⟨r, hr⟩
    choose reply hreply using hmax
    calc
      (∑ t, univ.sup (score t)) = ∑ t, score t (reply t) :=
        sum_congr rfl fun t _ ↦ hreply t
      _ ≤ (univ : Finset (T → Reply)).sup (fun f ↦ ∑ t, score t (f t)) :=
        le_sup (f := fun f ↦ ∑ t, score t (f t)) (mem_univ reply)

/-- The count with replies chosen separately for each first challenge equals the maximum over
all reply functions. For a nonempty reply type, a function can choose a best reply at every first
challenge. Both counts are zero when the reply type is empty. -/
theorem maxEventCount_eq_maxEventCountWithReply [DecidableEq T]
    (bad : W → T → Reply → S → Bool) :
    maxEventCount (fun (w : W × (T → Reply)) (c : T × S) ↦ bad w.1 c.1 (w.2 c.1) c.2) =
      maxEventCountWithReply bad := by
  rw [maxEventCount, maxEventCountWithReply, ← univ_product_univ, sup_product_left]
  refine sup_congr rfl fun w _ ↦ ?_
  have hcount (reply : T → Reply) :
      #{c : T × S | bad w c.1 (reply c.1) c.2 = true} =
        ∑ t : T, #{s : S | bad w t (reply t) s = true} := by
    calc
      _ = ∑ c : T × S, if bad w c.1 (reply c.1) c.2 = true then (1 : ℕ) else 0 :=
        (sum_boole (R := ℕ) _ univ).symm
      _ = _ := by
        rw [Fintype.sum_prod_type]
        exact sum_congr rfl fun t _ ↦ sum_boole (R := ℕ) _ univ
  simp_rw [hcount, maxEventCount]
  exact sup_pi_sum_eq_sum_sup fun t r ↦ #{s : S | bad w t r s = true}

end Reply

end Probability
